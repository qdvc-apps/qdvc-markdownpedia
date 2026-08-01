#!/usr/bin/env python3
"""
mdwiki.py - Build a static, Wikipedia-styled HTML site from a folder of Markdown files.

    python3 mdwiki.py ./notes -o ./outputs

Everything it emits is static and relative-path linked, so the result works when
opened straight off the filesystem (file:///...) with no server, no build step,
and no network access.

Features
    * Recursive Markdown discovery, mirrored folder structure in the output.
    * Wikipedia (Vector-skin) look: sidebar, article tabs, contents box, wikitables,
      category links, "Pages that link here", light/dark themes.
    * Wiki-style linking: [[Page Name]] / [[Page Name|label]] plus ordinary
      relative Markdown links (`../guide/intro.md#setup` is rewritten to
      `../guide/intro.html#setup`). Unresolved links render as red "new" links.
    * YAML-ish front matter for title / description / categories.
    * Auto-generated main page, folder indexes, all-pages index, category pages.
    * Client-side search over a generated JS index (works on file:// because it
      is loaded with a <script> tag rather than fetch()).
    * Zero required dependencies. If the `markdown` package is installed it is
      used for higher fidelity; otherwise a built-in Markdown subset renderer runs.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import posixpath
import re
import shutil
import sys
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

__version__ = "1.0.0"

MARKDOWN_SUFFIXES = {".md", ".markdown", ".mdown", ".mkd", ".mkdn"}
SKIP_DIR_NAMES = {".git", ".hg", ".svn", "node_modules", "__pycache__", ".venv", "venv"}
INDEX_STEMS = ("index", "readme", "home")


# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #

def slugify(text: str) -> str:
    """Lowercase ASCII slug, safe for filenames and URLs."""
    text = unicodedata.normalize("NFKD", text)
    text = text.encode("ascii", "ignore").decode("ascii")
    text = re.sub(r"[^A-Za-z0-9._-]+", "-", text).strip("-._")
    return (text.lower() or "page")[:80]


def anchor_id(text: str, used: set[str]) -> str:
    """MediaWiki-flavoured heading anchor: spaces become underscores."""
    plain = re.sub(r"<[^>]+>", "", text)
    plain = html.unescape(plain).strip()
    base = re.sub(r"\s+", "_", plain)
    base = re.sub(r'[#<>\[\]|{}"\'?%]', "", base) or "section"
    candidate, n = base, 1
    while candidate in used:
        n += 1
        candidate = f"{base}_{n}"
    used.add(candidate)
    return candidate


def humanize(name: str) -> str:
    """`getting-started_v2` -> `Getting started v2`."""
    text = re.sub(r"[-_]+", " ", name).strip()
    text = re.sub(r"\s+", " ", text)
    return text[:1].upper() + text[1:] if text else name


def strip_tags(markup: str) -> str:
    text = re.sub(r"(?is)<(script|style)\b.*?</\1>", " ", markup)
    text = re.sub(r"(?s)<[^>]+>", " ", text)
    text = html.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def rel_url(from_dir: str, to_path: str) -> str:
    """URL-quoted relative link from an output directory to an output file."""
    rel = posixpath.relpath(to_path, from_dir or ".")
    return quote(rel)


def esc(text: str) -> str:
    return html.escape(text, quote=True)


# --------------------------------------------------------------------------- #
# Front matter
# --------------------------------------------------------------------------- #

FRONT_MATTER_RE = re.compile(r"\A\ufeff?---[ \t]*\r?\n(.*?)\r?\n(?:---|\.\.\.)[ \t]*(?:\r?\n|\Z)", re.S)


def parse_front_matter(text: str) -> tuple[dict, str]:
    """Parse a deliberately small YAML subset: scalars, inline lists, dash lists."""
    match = FRONT_MATTER_RE.match(text)
    if not match:
        return {}, text

    meta: dict[str, object] = {}
    key: str | None = None
    for raw in match.group(1).splitlines():
        line = raw.rstrip()
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        item = re.match(r"^\s*-\s+(.*)$", line)
        if item and key:
            meta.setdefault(key, [])
            if isinstance(meta[key], list):
                meta[key].append(_scalar(item.group(1)))
            continue
        pair = re.match(r"^([A-Za-z0-9_.-]+)\s*:\s*(.*)$", line)
        if not pair:
            continue
        key, value = pair.group(1).lower(), pair.group(2).strip()
        if value == "":
            meta[key] = []
        elif value.startswith("[") and value.endswith("]"):
            meta[key] = _split_list(value[1:-1])
        else:
            meta[key] = _scalar(value)
    return meta, text[match.end():]


def _split_list(text: str) -> list[str]:
    """Split `a, "b, c", d` on commas that sit outside quotes."""
    parts, buf, quote_char = [], "", ""
    for ch in text:
        if quote_char:
            if ch == quote_char:
                quote_char = ""
            else:
                buf += ch
        elif ch in "\"'":
            quote_char = ch
        elif ch == ",":
            parts.append(buf)
            buf = ""
        else:
            buf += ch
    parts.append(buf)
    return [p.strip() for p in parts if p.strip()]


def _scalar(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
        value = value[1:-1]
    return value.strip()


def meta_list(meta: dict, *keys: str) -> list[str]:
    for key in keys:
        if key not in meta:
            continue
        value = meta[key]
        if isinstance(value, list):
            return [str(v).strip() for v in value if str(v).strip()]
        if isinstance(value, str) and value.strip():
            return _split_list(value.replace(";", ","))
    return []


# --------------------------------------------------------------------------- #
# Built-in Markdown renderer (fallback when `markdown` is not installed)
# --------------------------------------------------------------------------- #

class MiniMarkdown:
    """A compact, dependency-free renderer for common Markdown constructs."""

    FENCE = re.compile(r"^(\s{0,3})(`{3,}|~{3,})\s*([A-Za-z0-9_+#.-]*)\s*$")
    ATX = re.compile(r"^\s{0,3}(#{1,6})\s+(.*?)\s*#*\s*$")
    HR = re.compile(r"^\s{0,3}(?:(?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})$")
    QUOTE = re.compile(r"^\s{0,3}>[ \t]?(.*)$")
    ITEM = re.compile(r"^(\s*)([-*+]|\d{1,9}[.)])([ \t]+)(.*)$")
    SETEXT = re.compile(r"^\s{0,3}(=+|-+)\s*$")
    TABLE_SEP = re.compile(r"^\s{0,3}\|?[ \t]*:?-+:?[ \t]*(\|[ \t]*:?-+:?[ \t]*)*\|?\s*$")
    HTML_OPEN = re.compile(r"^\s{0,3}</?[A-Za-z][A-Za-z0-9-]*")
    RAW_TAGS = (
        "br|hr|b|i|em|strong|del|s|u|sup|sub|kbd|mark|small|abbr|code|span|div|p|"
        "img|a|input|figure|figcaption|details|summary|table|thead|tbody|tfoot|tr|th|td|"
        "ul|ol|li|dl|dt|dd|blockquote|section|aside|center|caption|colgroup|col"
    )
    RAW_TAG_RE = re.compile(rf"&lt;(/?(?:{RAW_TAGS})(?:\s[^<>]*?)?/?)&gt;", re.I)

    def __init__(self) -> None:
        self._store: list[str] = []
        self._refs: dict[str, tuple[str, str]] = {}

    # -- public ------------------------------------------------------------ #

    def convert(self, text: str) -> str:
        self._store = []
        self._refs = {}
        text = text.replace("\r\n", "\n").replace("\r", "\n").expandtabs(4)
        lines = self._extract_refs(text.split("\n"))
        return self._blocks(lines)

    # -- block level ------------------------------------------------------- #

    def _extract_refs(self, lines: list[str]) -> list[str]:
        pattern = re.compile(r'^\s{0,3}\[([^\]]+)\]:\s*(\S+)(?:\s+["(]([^")]*)[")])?\s*$')
        kept = []
        for line in lines:
            found = pattern.match(line)
            if found:
                self._refs[found.group(1).lower()] = (found.group(2), found.group(3) or "")
            else:
                kept.append(line)
        return kept

    def _is_block_start(self, line: str) -> bool:
        return bool(
            not line.strip()
            or self.FENCE.match(line)
            or self.ATX.match(line)
            or self.HR.match(line)
            or self.QUOTE.match(line)
            or self.ITEM.match(line)
            or self.HTML_OPEN.match(line)
        )

    def _blocks(self, lines: list[str]) -> str:
        out: list[str] = []
        i, total = 0, len(lines)
        while i < total:
            line = lines[i]
            if not line.strip():
                i += 1
                continue

            fence = self.FENCE.match(line)
            if fence:
                marker, lang = fence.group(2), fence.group(3)
                closing = re.compile(rf"^\s{{0,3}}{re.escape(marker[0])}{{{len(marker)},}}\s*$")
                i += 1
                buf: list[str] = []
                while i < total and not closing.match(lines[i]):
                    buf.append(lines[i])
                    i += 1
                i += 1
                cls = f' class="language-{esc(lang)}"' if lang else ""
                out.append(f"<pre><code{cls}>{html.escape(chr(10).join(buf))}</code></pre>")
                continue

            heading = self.ATX.match(line)
            if heading:
                level = len(heading.group(1))
                out.append(f"<h{level}>{self.inline(heading.group(2))}</h{level}>")
                i += 1
                continue

            if self.HR.match(line):
                out.append("<hr>")
                i += 1
                continue

            if self.QUOTE.match(line):
                buf, i = self._collect_quote(lines, i)
                out.append(f"<blockquote>{self._blocks(buf)}</blockquote>")
                continue

            if self.ITEM.match(line):
                markup, i = self._list(lines, i)
                out.append(markup)
                continue

            if "|" in line and i + 1 < total and self.TABLE_SEP.match(lines[i + 1]):
                markup, i = self._table(lines, i)
                out.append(markup)
                continue

            if self.HTML_OPEN.match(line):
                buf = []
                while i < total and lines[i].strip():
                    buf.append(lines[i])
                    i += 1
                out.append("\n".join(buf))
                continue

            if line.startswith("    "):
                buf = []
                while i < total and (lines[i].startswith("    ") or not lines[i].strip()):
                    buf.append(lines[i][4:])
                    i += 1
                while buf and not buf[-1].strip():
                    buf.pop()
                out.append(f"<pre><code>{html.escape(chr(10).join(buf))}</code></pre>")
                continue

            # paragraph (with setext heading support)
            buf = [line]
            i += 1
            while i < total and not self._is_block_start(lines[i]):
                setext = self.SETEXT.match(lines[i])
                if setext and len(buf) == 1:
                    level = 1 if setext.group(1).startswith("=") else 2
                    out.append(f"<h{level}>{self.inline(buf[0].strip())}</h{level}>")
                    buf = []
                    i += 1
                    break
                if "|" in lines[i] and self.TABLE_SEP.match(lines[i]):
                    break
                buf.append(lines[i])
                i += 1
            if buf:
                out.append(f"<p>{self.inline(chr(10).join(b.strip() for b in buf))}</p>")
        return "\n".join(out)

    def _collect_quote(self, lines: list[str], i: int) -> tuple[list[str], int]:
        buf: list[str] = []
        while i < len(lines):
            quoted = self.QUOTE.match(lines[i])
            if quoted:
                buf.append(quoted.group(1))
            elif lines[i].strip() and not self._is_block_start(lines[i]):
                buf.append(lines[i])  # lazy continuation
            else:
                break
            i += 1
        return buf, i

    def _list(self, lines: list[str], i: int) -> tuple[str, int]:
        first = self.ITEM.match(lines[i])
        assert first
        base_indent = len(first.group(1))
        ordered = first.group(2)[-1] in ".)"
        start = first.group(2)[:-1] if ordered else ""
        items: list[list[str]] = []
        loose = False

        while i < len(lines):
            probe = i
            while probe < len(lines) and not lines[probe].strip():
                probe += 1  # a blank line only separates items, it does not end the list
            if probe >= len(lines):
                break
            item = self.ITEM.match(lines[probe])
            if not item or len(item.group(1)) < base_indent:
                break
            if len(item.group(1)) > base_indent and items:
                break  # deeper marker handled as continuation below
            if (item.group(2)[-1] in ".)") != ordered:
                break
            if probe > i:
                loose = True
            i = probe
            offset = len(item.group(1)) + len(item.group(2)) + len(item.group(3))
            chunk = [item.group(4)]
            i += 1
            blanks = 0
            while i < len(lines):
                current = lines[i]
                if not current.strip():
                    nxt = lines[i + 1] if i + 1 < len(lines) else ""
                    if nxt.strip() and (len(nxt) - len(nxt.lstrip())) >= offset:
                        chunk.append("")
                        blanks += 1
                        i += 1
                        continue
                    break
                indent = len(current) - len(current.lstrip())
                if indent >= offset:
                    chunk.append(current[offset:])
                    i += 1
                    continue
                if self.ITEM.match(current) or self._is_block_start(current):
                    break
                chunk.append(current.strip())  # lazy paragraph continuation
                i += 1
            if blanks:
                loose = True
            items.append(chunk)

        rendered = []
        for chunk in items:
            body = "\n".join(chunk)
            task = re.match(r"^\[([ xX])\]\s+(.*)$", body, re.S)
            prefix = ""
            if task:
                checked = " checked" if task.group(1).lower() == "x" else ""
                prefix = f'<input type="checkbox" disabled{checked}> '
                body = task.group(2)
            simple = not loose and not any(
                self._is_block_start(l) or self.ITEM.match(l) for l in chunk[1:]
            ) and "\n" not in body.strip()
            inner = self.inline(body.strip()) if simple else self._blocks(body.split("\n"))
            cls = ' class="task-list-item"' if task else ""
            rendered.append(f"<li{cls}>{prefix}{inner}</li>")

        tag = "ol" if ordered else "ul"
        attrs = f' start="{int(start)}"' if ordered and start.isdigit() and int(start) != 1 else ""
        return f"<{tag}{attrs}>\n" + "\n".join(rendered) + f"\n</{tag}>", i

    def _table(self, lines: list[str], i: int) -> tuple[str, int]:
        def cells(row: str) -> list[str]:
            row = row.strip()
            row = row[1:] if row.startswith("|") else row
            row = row[:-1] if row.endswith("|") else row
            parts, buf, escaped = [], "", False
            for ch in row:
                if escaped:
                    buf += ch
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == "|":
                    parts.append(buf)
                    buf = ""
                else:
                    buf += ch
            parts.append(buf)
            return [p.strip() for p in parts]

        headers = cells(lines[i])
        aligns = []
        for spec in cells(lines[i + 1]):
            left, right = spec.startswith(":"), spec.endswith(":")
            aligns.append("center" if left and right else "right" if right else "left" if left else "")
        i += 2
        rows = []
        while i < len(lines) and lines[i].strip() and "|" in lines[i]:
            rows.append(cells(lines[i]))
            i += 1

        def style(idx: int) -> str:
            align = aligns[idx] if idx < len(aligns) else ""
            return f' style="text-align:{align}"' if align else ""

        out = ['<table class="wikitable">', "<thead>", "<tr>"]
        out += [f"<th{style(n)}>{self.inline(c)}</th>" for n, c in enumerate(headers)]
        out += ["</tr>", "</thead>", "<tbody>"]
        for row in rows:
            out.append("<tr>")
            out += [f"<td{style(n)}>{self.inline(c)}</td>" for n, c in enumerate(row)]
            out.append("</tr>")
        out += ["</tbody>", "</table>"]
        return "\n".join(out), i

    # -- inline level ------------------------------------------------------ #

    def _stash(self, markup: str) -> str:
        self._store.append(markup)
        return f"\x00{len(self._store) - 1}\x00"

    def inline(self, text: str) -> str:
        text = re.sub(r"(`+)(.+?)\1", lambda m: self._stash(f"<code>{html.escape(m.group(2))}</code>"), text, flags=re.S)
        text = re.sub(r"\\([\\`*_{}\[\]()#+\-.!<>|~])", lambda m: self._stash(html.escape(m.group(1))), text)
        text = html.escape(text, quote=False)

        def link(match: re.Match) -> str:
            label, target, title = match.group(1), match.group(2).strip(), match.group(3)
            if target.startswith("<") and target.endswith(">"):
                target = target[1:-1]
            attrs = f' title="{esc(title)}"' if title else ""
            return self._stash(f'<a href="{esc(target)}"{attrs}>{self.inline(label)}</a>')

        def image(match: re.Match) -> str:
            alt, target, title = match.group(1), match.group(2).strip(), match.group(3)
            if target.startswith("<") and target.endswith(">"):
                target = target[1:-1]
            attrs = f' title="{esc(title)}"' if title else ""
            return self._stash(f'<img src="{esc(target)}" alt="{esc(alt)}"{attrs} loading="lazy">')

        def reference(match: re.Match) -> str:
            label = match.group(1)
            key = (match.group(2) or label).lower()
            if key not in self._refs:
                return match.group(0)
            target, title = self._refs[key]
            attrs = f' title="{esc(title)}"' if title else ""
            return self._stash(f'<a href="{esc(target)}"{attrs}>{self.inline(label)}</a>')

        bracket = r"((?:[^\[\]]|\[[^\[\]]*\])*)"
        paren = r"(<[^>]*>|[^()\s]*(?:\([^()\s]*\))?[^()\s]*)"
        text = re.sub(rf"!\[{bracket}\]\(\s*{paren}(?:\s+[\"']([^\"']*)[\"'])?\s*\)", image, text)
        text = re.sub(rf"\[{bracket}\]\(\s*{paren}(?:\s+[\"']([^\"']*)[\"'])?\s*\)", link, text)
        text = re.sub(rf"\[{bracket}\]\[([^\]]*)\]", reference, text)
        text = re.sub(r"<((?:https?|mailto):[^>\s]+)>", lambda m: self._stash(f'<a href="{esc(m.group(1))}">{esc(m.group(1))}</a>'), text)

        text = re.sub(r"\*\*\*(?=\S)(.+?)(?<=\S)\*\*\*", r"<strong><em>\1</em></strong>", text, flags=re.S)
        text = re.sub(r"\*\*(?=\S)(.+?)(?<=\S)\*\*", r"<strong>\1</strong>", text, flags=re.S)
        text = re.sub(r"\*(?=\S)(.+?)(?<=\S)\*", r"<em>\1</em>", text, flags=re.S)
        text = re.sub(r"(?<![A-Za-z0-9_])___(?=\S)(.+?)(?<=\S)___(?![A-Za-z0-9_])", r"<strong><em>\1</em></strong>", text, flags=re.S)
        text = re.sub(r"(?<![A-Za-z0-9_])__(?=\S)(.+?)(?<=\S)__(?![A-Za-z0-9_])", r"<strong>\1</strong>", text, flags=re.S)
        text = re.sub(r"(?<![A-Za-z0-9_])_(?=\S)(.+?)(?<=\S)_(?![A-Za-z0-9_])", r"<em>\1</em>", text, flags=re.S)
        text = re.sub(r"~~(?=\S)(.+?)(?<=\S)~~", r"<del>\1</del>", text, flags=re.S)
        text = re.sub(r"(?<![\w\"'>=/])((?:https?://|www\.)[^\s<>\"')\]]+)", lambda m: self._stash(f'<a href="{esc(m.group(1))}">{esc(m.group(1))}</a>'), text)
        text = re.sub(r"[ \t]{2,}\n", "<br>\n", text)
        text = self.RAW_TAG_RE.sub(r"<\1>", text)

        while "\x00" in text:
            text = re.sub(r"\x00(\d+)\x00", lambda m: self._store[int(m.group(1))], text)
        return text


def make_renderer(engine: str, verbose: bool = False):
    """Return a `str -> str` Markdown converter."""
    if engine in ("auto", "markdown"):
        try:
            import markdown  # type: ignore

            extras = []
            try:  # `extra` has no strikethrough; add the GFM spelling of it.
                from markdown.extensions import Extension  # type: ignore
                from markdown.inlinepatterns import SimpleTagInlineProcessor  # type: ignore

                class _Strikethrough(Extension):
                    def extendMarkdown(self, md):  # noqa: N802 (library API)
                        md.inlinePatterns.register(
                            SimpleTagInlineProcessor(r"(~{2})(.+?)~{2}", "del"), "mdwiki-del", 175
                        )

                extras.append(_Strikethrough())
            except Exception:
                pass

            # `toc` is deliberately absent: heading anchors are generated here in
            # MediaWiki style (Quick_facts, not quick-facts) for both engines.
            for extensions in (
                ["extra", "sane_lists", "admonition", "attr_list"],
                ["extra", "sane_lists"],
                ["extra"],
                [],
            ):
                try:
                    md = markdown.Markdown(extensions=extensions + extras)
                    md.convert("# probe")
                    md.reset()
                    if verbose:
                        print(f"  markdown engine: python-markdown {getattr(markdown, '__version__', '?')}")
                    return lambda text, _md=md: (_md.reset(), _md.convert(text))[1]
                except Exception:
                    continue
        except ImportError:
            if engine == "markdown":
                print("error: --engine markdown requires `pip install markdown`", file=sys.stderr)
                raise SystemExit(2)
    if verbose:
        print("  markdown engine: built-in (install `markdown` for fuller syntax support)")
    return lambda text: MiniMarkdown().convert(text)


# --------------------------------------------------------------------------- #
# Page model
# --------------------------------------------------------------------------- #

@dataclass
class Page:
    out_path: str                      # posix path relative to the output root
    title: str
    src: Path | None = None            # source .md file, if any
    src_rel: str = ""                  # source path relative to the input root
    meta: dict = field(default_factory=dict)
    body: str = ""
    raw: str = ""
    headings: list[tuple[int, str, str]] = field(default_factory=list)
    text: str = ""
    mtime: float = 0.0
    kind: str = "article"              # article | folder | special | main
    categories: list[str] = field(default_factory=list)
    links_out: set[str] = field(default_factory=set)
    source_copy: str | None = None

    @property
    def out_dir(self) -> str:
        return posixpath.dirname(self.out_path)

    @property
    def depth(self) -> int:
        return self.out_path.count("/")

    def link_from(self, from_dir: str) -> str:
        return rel_url(from_dir, self.out_path)


# --------------------------------------------------------------------------- #
# Builder
# --------------------------------------------------------------------------- #

class SiteBuilder:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.input_root = args.input.resolve()
        self.output_root = args.output.resolve()
        self.render_markdown = make_renderer(args.engine, args.verbose)
        self.pages: list[Page] = []
        self.by_source: dict[str, Page] = {}     # input-relative posix md path -> Page
        self.by_title: dict[str, Page] = {}      # lowercase title/stem -> Page
        self.by_output: dict[str, Page] = {}
        self.assets: dict[str, Path] = {}        # output-relative posix path -> source file
        self.dirs: dict[str, list[str]] = {}     # input-relative dir -> child names
        self.special_dir = "special"
        self.broken: list[tuple[str, str]] = []
        self.stats = {"pages": 0, "assets": 0, "categories": 0}

    # -- orchestration ----------------------------------------------------- #

    def build(self) -> None:
        self.log(f"mdwiki {__version__}")
        self.log(f"  input : {self.input_root}")
        self.log(f"  output: {self.output_root}")
        if not self.input_root.is_dir():
            raise SystemExit(f"error: input folder not found: {self.input_root}")

        self.scan()
        if not self.pages:
            raise SystemExit(f"error: no Markdown files found under {self.input_root}")
        self.pick_special_dir()
        self.assign_index_paths()
        self.parse_pages()
        self.index_pages()
        self.resolve_links()
        self.add_generated_pages()
        self.write_site()
        self.report()

    def log(self, message: str) -> None:
        if not self.args.quiet:
            print(message)

    # -- discovery --------------------------------------------------------- #

    def scan(self) -> None:
        output_inside = self._is_inside(self.output_root, self.input_root)
        for dirpath, dirnames, filenames in os.walk(self.input_root):
            here = Path(dirpath)
            dirnames[:] = sorted(
                d for d in dirnames
                if d not in SKIP_DIR_NAMES
                and (self.args.include_hidden or not d.startswith("."))
                and not (output_inside and (here / d).resolve() == self.output_root)
            )
            rel_dir = self._rel(here)
            self.dirs.setdefault(rel_dir, [])
            for name in sorted(dirnames):
                self.dirs[rel_dir].append(posixpath.join(rel_dir, name) if rel_dir else name)

            for name in sorted(filenames):
                if not self.args.include_hidden and name.startswith("."):
                    continue
                path = here / name
                rel = self._rel(path)
                if path.suffix.lower() in MARKDOWN_SUFFIXES:
                    page = Page(
                        out_path=re.sub(r"\.[^./]+$", "", rel) + ".html",
                        title="",
                        src=path,
                        src_rel=rel,
                        mtime=path.stat().st_mtime,
                    )
                    self.pages.append(page)
                else:
                    self.assets[rel] = path

    def _rel(self, path: Path) -> str:
        rel = os.path.relpath(path, self.input_root)
        return "" if rel == "." else Path(rel).as_posix()

    @staticmethod
    def _is_inside(child: Path, parent: Path) -> bool:
        try:
            child.relative_to(parent)
            return True
        except ValueError:
            return False

    def pick_special_dir(self) -> None:
        taken = {p.out_path.split("/")[0] for p in self.pages} | {a.split("/")[0] for a in self.assets}
        name = "special"
        while name in taken:
            name += "_"
        self.special_dir = name

    def assign_index_paths(self) -> None:
        """Map the index/readme/home file of each folder onto `<folder>/index.html`.

        Browsers opening a folder from disk look for index.html, so the wiki's
        entry point should be one even when the source is called README.md.
        """
        by_dir: dict[str, list[Page]] = {}
        for page in self.pages:
            by_dir.setdefault(posixpath.dirname(page.src_rel), []).append(page)
        for rel_dir, group in by_dir.items():
            claimed = {p.out_path for p in group}
            target = posixpath.join(rel_dir, "index.html") if rel_dir else "index.html"
            if target in claimed:
                continue  # a real index.md already owns it
            ranked = sorted(
                (p for p in group if Path(p.src_rel).stem.lower() in INDEX_STEMS),
                key=lambda p: INDEX_STEMS.index(Path(p.src_rel).stem.lower()),
            )
            if ranked:
                ranked[0].out_path = target

    # -- parsing ----------------------------------------------------------- #

    def parse_pages(self) -> None:
        for page in self.pages:
            assert page.src is not None
            try:
                text = page.src.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                text = page.src.read_text(encoding="utf-8", errors="replace")
            page.meta, content = parse_front_matter(text)
            page.raw = text
            page.categories = meta_list(page.meta, "categories", "category", "tags", "tag")

            content = self._expand_wikilinks(content)
            content = self._expand_tasklists(content)
            body = self.render_markdown(content)
            body, first_h1 = self._lift_title(body)

            title = str(page.meta.get("title") or "").strip() or first_h1
            if not title:
                stem = Path(page.src_rel).stem
                title = humanize(Path(page.src_rel).parent.name or self.args.site_name) if stem.lower() in INDEX_STEMS and Path(page.src_rel).parent.name else humanize(stem)
            page.title = title
            page.body = body
            page.text = strip_tags(body)[: self.args.index_chars]

            if self.args.copy_source:
                name = Path(page.src_rel).name
                page.source_copy = posixpath.join(page.out_dir, name) if page.out_dir else name

    def _expand_wikilinks(self, text: str) -> str:
        """`[[Target|label]]` -> `[label](wiki:Target)` (URL-encoded target)."""
        def repl(match: re.Match) -> str:
            inner = match.group(1).strip()
            target, _, label = inner.partition("|")
            target, label = target.strip(), (label.strip() or target.strip())
            target, _, fragment = target.partition("#")
            encoded = quote(target.strip(), safe="/")
            anchor = "#" + quote(fragment.strip().replace(" ", "_")) if fragment.strip() else ""
            return f"[{label}](wiki:{encoded}{anchor})"

        placeholders: list[str] = []

        def hide(match: re.Match) -> str:
            placeholders.append(match.group(0))
            return f"\x01{len(placeholders) - 1}\x01"

        text = re.sub(r"```.*?```|~~~.*?~~~|`[^`\n]*`", hide, text, flags=re.S)
        text = re.sub(r"\[\[([^\]\n]+)\]\]", repl, text)
        return re.sub(r"\x01(\d+)\x01", lambda m: placeholders[int(m.group(1))], text)

    @staticmethod
    def _expand_tasklists(text: str) -> str:
        """`- [x] done` -> a list item holding a disabled checkbox, for either engine."""
        def repl(match: re.Match) -> str:
            checked = " checked" if match.group(2).lower() == "x" else ""
            return f'{match.group(1)}<input type="checkbox" class="task-checkbox" disabled{checked}> '

        return re.sub(r"(?m)^(\s*(?:[-*+]|\d{1,9}[.)])\s+)\[([ xX])\]\s+", repl, text)

    def _lift_title(self, body: str) -> tuple[str, str]:
        """Remove a leading <h1> and return its text (the shell renders the title)."""
        match = re.match(r"\s*<h1[^>]*>(.*?)</h1>\s*", body, re.S | re.I)
        if not match:
            return body, ""
        return body[match.end():], strip_tags(match.group(1))

    def index_pages(self) -> None:
        for page in self.pages:
            self.by_source[page.src_rel] = page
            self.by_output[page.out_path] = page
            for key in {page.title.lower(), Path(page.src_rel).stem.lower(), page.out_path.lower()}:
                self.by_title.setdefault(key, page)

        # Folders that contain Markdown at any depth; asset-only folders get no page.
        content_dirs: set[str] = set()
        for page in self.pages:
            walked = posixpath.dirname(page.src_rel)
            while True:
                content_dirs.add(walked)
                if not walked:
                    break
                walked = posixpath.dirname(walked)

        # Folder pages: use an existing index/readme/home file, else generate one.
        self.folder_pages: dict[str, Page] = {}
        for rel_dir in sorted(d for d in self.dirs if d in content_dirs):
            candidate = None
            for page in self.pages:
                parent = posixpath.dirname(page.src_rel)
                if parent == rel_dir and Path(page.src_rel).stem.lower() in INDEX_STEMS:
                    candidate = page
                    break
            if candidate:
                self.folder_pages[rel_dir] = candidate
            elif rel_dir:
                self.folder_pages[rel_dir] = Page(
                    out_path=posixpath.join(rel_dir, "index.html"),
                    title=humanize(posixpath.basename(rel_dir)),
                    kind="folder",
                    src_rel=rel_dir,
                )

    # -- link rewriting ---------------------------------------------------- #

    TAG_RE = re.compile(r"<(a|img|source|video|audio|iframe|embed)\b([^>]*?)(/?)>", re.I | re.S)
    ATTR_RE = re.compile(r"""(?P<attr>\b(?:href|src|poster)\s*=\s*)(?P<q>["'])(?P<url>.*?)(?P=q)""", re.S | re.I)

    def resolve_links(self) -> None:
        for page in self.pages:
            page.body = self.TAG_RE.sub(lambda m: self._rewrite_tag(m, page), page.body)

        graph: dict[str, set[str]] = {}
        for page in self.pages:
            for target in page.links_out:
                graph.setdefault(target, set()).add(page.out_path)
        self.backlinks = graph

    def _rewrite_tag(self, match: re.Match, page: Page) -> str:
        tag, attrs, closer = match.group(1), match.group(2), match.group(3)
        added: list[str] = []

        def rewrite(attr_match: re.Match) -> str:
            url = html.unescape(attr_match.group("url")).strip()
            new_url, css = self._resolve_url(url, page)
            if css and tag.lower() == "a" and attr_match.group("attr").lower().startswith("href"):
                added.append(css)
            return f'{attr_match.group("attr")}"{esc(new_url)}"'

        attrs = self.ATTR_RE.sub(rewrite, attrs)
        if added:
            existing = re.search(r'\bclass\s*=\s*(["\'])(.*?)\1', attrs, re.S)
            if existing:
                merged = " ".join(existing.group(2).split() + added)
                attrs = attrs[: existing.start()] + f'class="{esc(merged)}"' + attrs[existing.end():]
            else:
                attrs = attrs.rstrip() + f' class="{esc(" ".join(added))}"'
        return f"<{tag}{attrs}{closer}>"

    def _resolve_url(self, url: str, page: Page) -> tuple[str, str]:
        if not url or url.startswith("#") or url.startswith("//"):
            return url, ""
        parts = urlsplit(url)
        if parts.scheme and parts.scheme.lower() != "wiki":
            return url, "external" if parts.scheme.lower() in ("http", "https") else ""

        from_dir = page.out_dir

        if parts.scheme.lower() == "wiki":
            name = unquote(parts.path).strip()
            target = self.by_title.get(name.lower()) or self.by_title.get(slugify(name))
            if not target:
                stem = name.rsplit("/", 1)[-1].lower()
                target = self.by_title.get(stem)
            if target:
                page.links_out.add(target.out_path)
                return target.link_from(from_dir) + self._fragment(parts.fragment), ""
            self.broken.append((page.src_rel or page.out_path, f"[[{name}]]"))
            return quote(slugify(name)) + ".html", "new"

        raw_path = unquote(parts.path)
        if not raw_path:
            return url, ""
        base_dir = posixpath.dirname(page.src_rel) if page.src is not None else page.src_rel
        candidate = posixpath.normpath(posixpath.join(base_dir, raw_path)) if not raw_path.startswith("/") else raw_path.lstrip("/")
        candidate = "" if candidate == "." else candidate

        target = self._lookup_path(candidate)
        if isinstance(target, Page):
            page.links_out.add(target.out_path)
            return target.link_from(from_dir) + self._fragment(parts.fragment) + self._query(parts.query), ""
        if isinstance(target, str):  # asset
            return rel_url(from_dir, target) + self._fragment(parts.fragment) + self._query(parts.query), ""

        self.broken.append((page.src_rel or page.out_path, url))
        guess = re.sub(r"\.(md|markdown|mdown|mkd|mkdn)$", ".html", candidate, flags=re.I) or "index.html"
        return rel_url(from_dir, guess) + self._fragment(parts.fragment), "new"

    def _lookup_path(self, candidate: str) -> Page | str | None:
        if candidate in self.by_source:
            return self.by_source[candidate]
        if candidate in self.assets:
            return candidate
        stripped = candidate.rstrip("/")
        if stripped in self.folder_pages:
            return self.folder_pages[stripped]
        if candidate.lower().endswith(".html"):
            base = candidate[:-5]
            for suffix in MARKDOWN_SUFFIXES:
                if base + suffix in self.by_source:
                    return self.by_source[base + suffix]
        for suffix in MARKDOWN_SUFFIXES:
            if stripped + suffix in self.by_source:
                return self.by_source[stripped + suffix]
        for stem in INDEX_STEMS:
            for suffix in MARKDOWN_SUFFIXES:
                joined = posixpath.join(stripped, stem + suffix) if stripped else stem + suffix
                if joined in self.by_source:
                    return self.by_source[joined]
        return None

    @staticmethod
    def _fragment(fragment: str) -> str:
        return "#" + quote(unquote(fragment).replace(" ", "_"), safe="") if fragment else ""

    @staticmethod
    def _query(query: str) -> str:
        return "?" + query if query else ""

    # -- generated pages --------------------------------------------------- #

    def add_generated_pages(self) -> None:
        generated: list[Page] = []

        for rel_dir, page in sorted(self.folder_pages.items()):
            if page.kind == "folder":
                page.body = self._folder_body(rel_dir, page)
                page.text = strip_tags(page.body)[: self.args.index_chars]
                generated.append(page)

        # categories
        self.categories: dict[str, list[Page]] = {}
        for page in self.pages:
            for name in page.categories:
                self.categories.setdefault(name, []).append(page)
        self.category_pages: dict[str, Page] = {}
        used_slugs: set[str] = set()
        for name in sorted(self.categories, key=str.lower):
            slug = slugify(name)
            if slug in used_slugs:  # e.g. "Ünïcödé" and "Unicode" both slugify to `unicode`
                n = 2
                while f"{slug}-{n}" in used_slugs:
                    n += 1
                slug = f"{slug}-{n}"
            used_slugs.add(slug)
            cat = Page(
                out_path=f"{self.special_dir}/category-{slug}.html",
                title=f"Category: {name}",
                kind="special",
            )
            self.category_pages[name] = cat
        for name, cat in self.category_pages.items():
            members = sorted(self.categories[name], key=lambda p: p.title.lower())
            cat.body = self._list_body(
                f"Pages in category &#8220;{esc(name)}&#8221;",
                members,
                cat.out_dir,
                f"This category contains {len(members)} page{'s' if len(members) != 1 else ''}.",
            )
            cat.text = strip_tags(cat.body)[: self.args.index_chars]
            generated.append(cat)
        self.stats["categories"] = len(self.category_pages)

        # all pages
        self.all_pages_page = Page(
            out_path=f"{self.special_dir}/all-pages.html", title="All pages", kind="special"
        )
        self.all_pages_page.body = self._all_pages_body(self.all_pages_page.out_dir)
        generated.append(self.all_pages_page)

        # category index
        self.categories_page = Page(
            out_path=f"{self.special_dir}/categories.html", title="Categories", kind="special"
        )
        self.categories_page.body = self._categories_body(self.categories_page.out_dir)
        generated.append(self.categories_page)

        # main page
        root_page = self.folder_pages.get("")
        if root_page is not None and root_page.kind == "article":
            self.main_page = root_page
            root_page.kind = "main"
        else:
            self.main_page = Page(out_path="index.html", title="Main page", kind="main")
            self.main_page.body = self._main_body("")
            generated.append(self.main_page)

        self.pages.extend(generated)
        for page in generated:
            self.by_output[page.out_path] = page

    def _child_pages(self, rel_dir: str) -> tuple[list[Page], list[tuple[str, Page]]]:
        files = sorted(
            (p for p in self.pages
             if p.src is not None
             and posixpath.dirname(p.src_rel) == rel_dir
             and Path(p.src_rel).stem.lower() not in INDEX_STEMS),
            key=lambda p: p.title.lower(),
        )
        folders = sorted(
            ((child, self.folder_pages[child]) for child in self.dirs.get(rel_dir, []) if child in self.folder_pages),
            key=lambda pair: pair[1].title.lower(),
        )
        return files, folders

    def _folder_body(self, rel_dir: str, page: Page) -> str:
        files, folders = self._child_pages(rel_dir)
        out = [
            f'<p>This index page lists the contents of the <code>{esc(rel_dir or ".")}</code> '
            f"folder: {len(folders)} subfolder{'s' if len(folders) != 1 else ''} and "
            f"{len(files)} page{'s' if len(files) != 1 else ''}.</p>"
        ]
        if folders:
            out.append("<h2>Subfolders</h2>\n<ul class=\"page-list\">")
            for _, sub in folders:
                out.append(f'<li><a href="{esc(sub.link_from(page.out_dir))}">{esc(sub.title)}</a></li>')
            out.append("</ul>")
        if files:
            out.append("<h2>Pages</h2>\n<ul class=\"page-list\">")
            for child in files:
                blurb = self._blurb(child)
                extra = f' <span class="page-blurb">&mdash; {esc(blurb)}</span>' if blurb else ""
                out.append(f'<li><a href="{esc(child.link_from(page.out_dir))}">{esc(child.title)}</a>{extra}</li>')
            out.append("</ul>")
        if not files and not folders:
            out.append("<p class=\"empty\">This folder has no Markdown pages.</p>")
        return "\n".join(out)

    def _blurb(self, page: Page, limit: int = 140) -> str:
        text = str(page.meta.get("description") or "").strip() or page.text
        if len(text) > limit:
            text = text[:limit].rsplit(" ", 1)[0] + "\u2026"
        return text

    def _list_body(self, heading: str, members: list[Page], from_dir: str, intro: str) -> str:
        out = [f"<p>{intro}</p>", f"<h2>{heading}</h2>", '<ul class="page-list">']
        for member in members:
            out.append(f'<li><a href="{esc(member.link_from(from_dir))}">{esc(member.title)}</a></li>')
        out.append("</ul>")
        return "\n".join(out)

    def _all_pages_body(self, from_dir: str) -> str:
        articles = sorted((p for p in self.pages if p.src is not None), key=lambda p: p.title.lower())
        groups: dict[str, list[Page]] = {}
        for page in articles:
            first = page.title[:1].upper()
            groups.setdefault(first if first.isalnum() else "#", []).append(page)
        keys = sorted(groups, key=lambda k: (k == "#", k))
        out = [
            f"<p>This wiki has {len(articles)} page{'s' if len(articles) != 1 else ''}, "
            f"listed alphabetically.</p>",
            '<div class="letter-nav">' + " ".join(f'<a href="#letter-{esc(k)}">{esc(k)}</a>' for k in keys) + "</div>",
        ]
        for key in keys:
            out.append(f'<h2 id="letter-{esc(key)}">{esc(key)}</h2>')
            out.append('<ul class="page-list columns">')
            for page in groups[key]:
                out.append(f'<li><a href="{esc(page.link_from(from_dir))}">{esc(page.title)}</a></li>')
            out.append("</ul>")
        return "\n".join(out)

    def _categories_body(self, from_dir: str) -> str:
        if not self.category_pages:
            return (
                "<p>No categories yet. Add a <code>categories:</code> or <code>tags:</code> field to a page's "
                "front matter and they will be listed here.</p>\n"
                "<pre><code>---\ntitle: Kettle logic\ncategories: [Logic, Rhetoric]\n---</code></pre>"
            )
        out = [f"<p>This wiki has {len(self.category_pages)} categories.</p>", '<ul class="page-list columns">']
        for name, cat in self.category_pages.items():
            count = len(self.categories[name])
            out.append(
                f'<li><a href="{esc(cat.link_from(from_dir))}">{esc(name)}</a> '
                f'<span class="page-blurb">({count})</span></li>'
            )
        out.append("</ul>")
        return "\n".join(out)

    def _main_body(self, from_dir: str) -> str:
        articles = [p for p in self.pages if p.src is not None]
        recent = sorted(articles, key=lambda p: p.mtime, reverse=True)[:10]
        top_files, folders = self._child_pages("")

        out = [
            '<div class="mainpage-banner">',
            f"<h2>Welcome to {esc(self.args.site_name)}</h2>",
            f"<p>A static wiki built from {len(articles)} Markdown "
            f"file{'s' if len(articles) != 1 else ''}"
            f"{f' across {len(self.dirs) - 1} folders' if len(self.dirs) > 1 else ''}. "
            "Use the search box above, or start from the sections below.</p>",
            "</div>",
            '<div class="mainpage-columns">',
        ]
        out.append('<section class="mainpage-box"><h2>Sections</h2><ul class="page-list">')
        if folders:
            for _, folder in folders:
                out.append(f'<li><a href="{esc(folder.link_from(from_dir))}">{esc(folder.title)}</a></li>')
        for page in top_files[:12]:
            out.append(f'<li><a href="{esc(page.link_from(from_dir))}">{esc(page.title)}</a></li>')
        out.append("</ul></section>")

        out.append('<section class="mainpage-box"><h2>Recently updated</h2><ul class="page-list">')
        for page in recent:
            stamp = datetime.fromtimestamp(page.mtime).strftime("%d %b %Y")
            out.append(
                f'<li><a href="{esc(page.link_from(from_dir))}">{esc(page.title)}</a> '
                f'<span class="page-blurb">{esc(stamp)}</span></li>'
            )
        out.append("</ul></section>")
        out.append("</div>")
        out.append(
            f'<p class="mainpage-footnote">See <a href="{esc(self.all_pages_page.link_from(from_dir))}">all pages</a>'
            f' or browse <a href="{esc(self.categories_page.link_from(from_dir))}">categories</a>.</p>'
        )
        return "\n".join(out)

    # -- assembly ---------------------------------------------------------- #

    def write_site(self) -> None:
        if self.args.clean and self.output_root.exists():
            if self.output_root == self.input_root:
                raise SystemExit("error: refusing to --clean an output folder equal to the input folder")
            self.log(f"  cleaning {self.output_root}")
            if not self.args.dry_run:
                shutil.rmtree(self.output_root)

        for page in self.pages:
            used: set[str] = set()
            page.body, page.headings = self._decorate_headings(page.body, used)

        if self.args.dry_run:
            self.log("  dry run: nothing written")
            self.stats["pages"] = len(self.pages)
            self.stats["assets"] = len(self.assets)
            return

        for page in self.pages:
            markup = self._shell(page)
            self._write(page.out_path, markup)
            self.stats["pages"] += 1
            if page.source_copy and page.src is not None:
                target = self.output_root / page.source_copy
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(page.src, target)

        for rel, source in sorted(self.assets.items()):
            target = self.output_root / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
            self.stats["assets"] += 1

        self._write("assets/wiki.css", STYLESHEET)
        self._write("assets/wiki.js", SCRIPT)
        self._write("assets/search-index.js", self._search_index())
        self._write("assets/logo.svg", LOGO_SVG)

    def _write(self, rel: str, text: str) -> None:
        target = self.output_root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")

    def _decorate_headings(self, body: str, used: set[str]) -> tuple[str, list[tuple[int, str, str]]]:
        headings: list[tuple[int, str, str]] = []

        def repl(match: re.Match) -> str:
            level, attrs, inner = int(match.group(1)), match.group(2) or "", match.group(3)
            existing = re.search(r'\bid\s*=\s*["\']([^"\']+)["\']', attrs)
            if existing:
                ident = existing.group(1)
                used.add(ident)
                attrs = re.sub(r'\s*\bid\s*=\s*["\'][^"\']*["\']', "", attrs)
            else:
                ident = anchor_id(inner, used)
            text = strip_tags(inner)
            headings.append((level, ident, text))
            return (
                f'<h{level} id="{esc(ident)}"{attrs}>'
                f'<span class="mw-headline">{inner}</span>'
                f'<a class="heading-anchor" href="#{esc(ident)}" '
                f'aria-label="Permanent link to {esc(text)}">&#182;</a>'
                f"</h{level}>"
            )

        body = re.sub(r"<h([1-6])((?:\s[^>]*)?)>(.*?)</h\1>", repl, body, flags=re.S | re.I)
        return body, headings

    def _toc(self, page: Page) -> str:
        if self.args.no_toc or len(page.headings) < self.args.toc_min:
            return ""
        entries = [h for h in page.headings if h[0] <= self.args.toc_depth + 1]
        if len(entries) < self.args.toc_min:
            return ""

        out = ['<div id="toc" class="toc" role="navigation" aria-labelledby="toc-heading">',
               '<div class="toctitle"><h2 id="toc-heading">Contents</h2>',
               '<span class="toctogglespan">[<button type="button" class="toctogglebutton" '
               'data-action="toggle-toc" aria-expanded="true">hide</button>]</span></div>',
               '<ul class="toc-list">']
        levels: list[int] = []
        counters: list[int] = []
        for level, ident, text in entries:
            while levels and level < levels[-1]:
                levels.pop()
                counters.pop()
                out.append("</ul></li>")
            if levels and level > levels[-1]:
                out[-1] = out[-1][:-5] if out[-1].endswith("</li>") else out[-1]
                out.append("<ul>")
                levels.append(level)
                counters.append(0)
            elif not levels:
                levels.append(level)
                counters.append(0)
            counters[-1] += 1
            number = ".".join(str(c) for c in counters)
            out.append(
                f'<li class="toclevel-{len(levels)}"><a href="#{esc(ident)}">'
                f'<span class="tocnumber">{number}</span> '
                f'<span class="toctext">{esc(text)}</span></a></li>'
            )
        while len(levels) > 1:
            levels.pop()
            counters.pop()
            out.append("</ul></li>")
        out.append("</ul></div>")
        return "\n".join(out)

    def _breadcrumbs(self, page: Page) -> str:
        if page.kind == "main":
            return ""
        from_dir = page.out_dir
        crumbs = [f'<a href="{esc(self.main_page.link_from(from_dir))}">{esc(self.args.site_name)}</a>']
        parts = (posixpath.dirname(page.src_rel) if page.src is not None else page.src_rel).split("/")
        walked = ""
        for part in parts:
            if not part:
                continue
            walked = posixpath.join(walked, part) if walked else part
            folder = self.folder_pages.get(walked)
            label = esc(folder.title if folder else humanize(part))
            crumbs.append(
                f'<a href="{esc(folder.link_from(from_dir))}">{label}</a>' if folder else label
            )
        if page.kind == "special":
            crumbs.append("Special pages")
        if len(crumbs) == 1:
            return ""
        return '<div id="contentSub" class="breadcrumbs">' + ' <span class="crumb-sep">&#8250;</span> '.join(crumbs) + "</div>"

    def _catlinks(self, page: Page) -> str:
        if not page.categories:
            return ""
        from_dir = page.out_dir
        links = []
        for name in page.categories:
            cat = self.category_pages.get(name)
            links.append(
                f'<li><a href="{esc(cat.link_from(from_dir))}">{esc(name)}</a></li>' if cat else f"<li>{esc(name)}</li>"
            )
        return (
            '<div id="catlinks" class="catlinks"><div class="catlinks-inner">'
            f'<span class="catlinks-label">Categories</span>: <ul>{"".join(links)}</ul>'
            "</div></div>"
        )

    def _backlinks_box(self, page: Page) -> str:
        if self.args.no_backlinks:
            return ""
        sources = sorted(self.backlinks.get(page.out_path, set()))
        sources = [s for s in sources if s != page.out_path]
        if not sources:
            return ""
        from_dir = page.out_dir
        items = []
        for out_path in sources:
            other = self.by_output.get(out_path)
            if not other:
                continue
            items.append(f'<li><a href="{esc(other.link_from(from_dir))}">{esc(other.title)}</a></li>')
        if not items:
            return ""
        return (
            '<details class="whatlinkshere">'
            f"<summary>Pages that link here ({len(items)})</summary>"
            f'<ul class="page-list columns">{"".join(items)}</ul>'
            "</details>"
        )

    def _sidebar(self, page: Page) -> str:
        from_dir = page.out_dir
        base = ("../" * page.depth) or ""
        nav = [
            ('<div class="portal"><h3>Navigation</h3><ul>'),
            f'<li><a href="{esc(self.main_page.link_from(from_dir))}">Main page</a></li>',
            f'<li><a href="{esc(self.all_pages_page.link_from(from_dir))}">All pages</a></li>',
            f'<li><a href="{esc(self.categories_page.link_from(from_dir))}">Categories</a></li>',
            '<li><a href="#" data-action="random">Random page</a></li>',
            "</ul></div>",
        ]

        root_files, folders = self._child_pages("")
        if folders or root_files:
            nav.append('<div class="portal"><h3>Contents</h3><ul>')
            current = posixpath.dirname(page.src_rel) if page.src is not None else page.src_rel
            for rel_dir, folder in folders:
                open_here = current == rel_dir or current.startswith(rel_dir + "/")
                active = ' class="active"' if open_here else ""
                nav.append(f'<li{active}><a href="{esc(folder.link_from(from_dir))}">{esc(folder.title)}</a>')
                if open_here:
                    children, subfolders = self._child_pages(rel_dir)
                    if children or subfolders:
                        nav.append('<ul class="subnav">')
                        for _, sub in subfolders:
                            nav.append(f'<li><a href="{esc(sub.link_from(from_dir))}">{esc(sub.title)}</a></li>')
                        for child in children:
                            mark = ' class="active"' if child.out_path == page.out_path else ""
                            nav.append(f'<li{mark}><a href="{esc(child.link_from(from_dir))}">{esc(child.title)}</a></li>')
                        nav.append("</ul>")
                nav.append("</li>")
            for child in root_files[:15]:
                mark = ' class="active"' if child.out_path == page.out_path else ""
                nav.append(f'<li{mark}><a href="{esc(child.link_from(from_dir))}">{esc(child.title)}</a></li>')
            nav.append("</ul></div>")

        nav.append(
            '<div class="portal"><h3>Tools</h3><ul>'
            '<li><a href="#" data-action="print">Printable version</a></li>'
            '<li><a href="#" data-action="theme">Toggle dark mode</a></li>'
            "</ul></div>"
        )
        logo = base + "assets/logo.svg"
        return (
            '<div id="mw-panel" class="sidebar">'
            f'<a id="p-logo" href="{esc(self.main_page.link_from(from_dir))}" title="Visit the main page">'
            f'<img src="{esc(logo)}" alt="" width="90" height="90"></a>'
            f'<div class="site-name"><a href="{esc(self.main_page.link_from(from_dir))}">{esc(self.args.site_name)}</a></div>'
            + "".join(nav)
            + "</div>"
        )

    def _tabs(self, page: Page, has_toc: bool) -> str:
        tabs = ['<li class="selected"><span>Article</span></li>']
        if page.source_copy:
            tabs.append(
                f'<li><a href="{esc(rel_url(page.out_dir, page.source_copy))}">View source</a></li>'
            )
        actions = ['<li><a href="#" data-action="print">Print</a></li>']
        if has_toc:
            actions.insert(0, '<li><a href="#toc">Contents</a></li>')
        return (
            '<div id="left-navigation"><ul class="tabs">' + "".join(tabs) + "</ul></div>"
            '<div id="right-navigation"><ul class="tabs actions">' + "".join(actions) + "</ul></div>"
        )

    def _search_form(self, page: Page) -> str:
        return (
            '<div id="p-search" class="search" role="search">'
            '<label class="visually-hidden" for="searchInput">Search this wiki</label>'
            '<input type="search" id="searchInput" autocomplete="off" spellcheck="false" '
            'placeholder="Search this wiki" aria-controls="searchResults" aria-expanded="false">'
            '<button type="button" id="searchButton" data-action="search">Search</button>'
            '<ul id="searchResults" class="search-results" role="listbox" hidden></ul>'
            "</div>"
        )

    def _shell(self, page: Page) -> str:
        base = ("../" * page.depth) or ""
        toc = self._toc(page)
        described = self._blurb(page, 200)
        stamp = (
            datetime.fromtimestamp(page.mtime, tz=timezone.utc).strftime("%d %B %Y, %H:%M UTC")
            if page.mtime else ""
        )
        footer_bits = ["Built with mdwiki from Markdown sources."]
        if stamp:
            footer_bits.insert(0, f"This page was last modified on {esc(stamp)}.")

        title_suffix = "" if page.kind == "main" else f" &#8212; {esc(self.args.site_name)}"
        theme_attr = f' data-theme="{esc(self.args.theme)}"' if self.args.theme in ("light", "dark") else ""

        return f"""<!DOCTYPE html>
<html lang="{esc(self.args.lang)}"{theme_attr}>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="generator" content="mdwiki {__version__}">
<meta name="description" content="{esc(described)}">
<title>{esc(page.title)}{title_suffix}</title>
<link rel="stylesheet" href="{esc(base)}assets/wiki.css">
<link rel="icon" href="{esc(base)}assets/logo.svg" type="image/svg+xml">
</head>
<body class="page-{esc(page.kind)}" data-base="{esc(base)}" data-page="{esc(page.out_path)}">
<a class="visually-hidden skip-link" href="#mw-content-text">Skip to content</a>
<div id="mw-page-base"></div>
<div class="layout">
{self._sidebar(page)}
<div class="content-column">
<div id="mw-head">
<button type="button" class="menu-toggle" data-action="menu" aria-label="Show navigation">&#9776;</button>
{self._search_form(page)}
</div>
{self._tabs(page, bool(toc))}
<main id="content" class="mw-body">
<h1 id="firstHeading" class="firstHeading">{esc(page.title)}</h1>
<div id="siteSub">{esc(self.args.tagline)}</div>
{self._breadcrumbs(page)}
<div id="mw-content-text" class="mw-parser-output">
{toc}
{page.body}
</div>
{self._catlinks(page)}
{self._backlinks_box(page)}
<div class="printfooter">Retrieved from &#8220;{esc(page.out_path)}&#8221;</div>
</main>
<footer id="footer">
<p>{" ".join(footer_bits)}</p>
<ul class="footer-links">
<li><a href="{esc(self.main_page.link_from(page.out_dir))}">Main page</a></li>
<li><a href="{esc(self.all_pages_page.link_from(page.out_dir))}">All pages</a></li>
<li><a href="#" data-action="theme">Toggle dark mode</a></li>
</ul>
</footer>
</div>
</div>
<script src="{esc(base)}assets/search-index.js"></script>
<script src="{esc(base)}assets/wiki.js"></script>
</body>
</html>
"""

    def _search_index(self) -> str:
        records = []
        for page in sorted(self.pages, key=lambda p: p.title.lower()):
            records.append({
                "t": page.title,
                "u": page.out_path,
                "s": self._blurb(page, 180),
                "h": [h[2] for h in page.headings[:12]],
                "x": page.text[: self.args.index_chars],
                "c": page.categories,
            })
        payload = json.dumps(records, ensure_ascii=False, separators=(",", ":"))
        site = json.dumps({"name": self.args.site_name, "pages": len(records)}, ensure_ascii=False)
        return f"window.MDWIKI_SITE={site};\nwindow.MDWIKI_INDEX={payload};\n"

    # -- reporting --------------------------------------------------------- #

    def report(self) -> None:
        verb = "would write" if self.args.dry_run else "wrote"
        self.log(
            f"  {verb} {self.stats['pages']} pages, {self.stats['assets']} copied files, "
            f"{self.stats['categories']} categories"
        )
        if self.broken and not self.args.quiet:
            unique = sorted(set(self.broken))
            print(f"  {len(unique)} unresolved link(s) rendered as red links:")
            for src, target in unique[: self.args.max_warnings]:
                print(f"    {src}: {target}")
            if len(unique) > self.args.max_warnings:
                print(f"    ... and {len(unique) - self.args.max_warnings} more")
        if not self.args.dry_run:
            entry = (self.output_root / self.main_page.out_path).as_uri()
            self.log(f"  open {entry}")


# --------------------------------------------------------------------------- #
# Static assets
# --------------------------------------------------------------------------- #

LOGO_SVG = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100" width="100" height="100" role="img" aria-label="Wiki logo">
  <defs><radialGradient id="g" cx="35%" cy="30%" r="75%">
    <stop offset="0" stop-color="#ffffff"/><stop offset="1" stop-color="#dcdcdc"/>
  </radialGradient></defs>
  <circle cx="50" cy="50" r="44" fill="url(#g)" stroke="#8f9296" stroke-width="1.5"/>
  <g fill="none" stroke="#8f9296" stroke-width="1.1">
    <ellipse cx="50" cy="50" rx="44" ry="17"/><ellipse cx="50" cy="50" rx="44" ry="33"/>
    <ellipse cx="50" cy="50" rx="17" ry="44"/><ellipse cx="50" cy="50" rx="33" ry="44"/>
    <line x1="6" y1="50" x2="94" y2="50"/><line x1="50" y1="6" x2="50" y2="94"/>
  </g>
  <g fill="#54595d" font-family="Georgia, 'Times New Roman', serif" font-size="17" text-anchor="middle">
    <text x="31" y="40">M</text><text x="69" y="40">&#9633;</text>
    <text x="31" y="72">&#9633;</text><text x="69" y="72">D</text>
  </g>
</svg>
"""

STYLESHEET = """/* mdwiki - Wikipedia-flavoured stylesheet. Static, no webfonts, works on file://. */
:root {
  --page-bg: #f6f6f6;
  --body-bg: #ffffff;
  --text: #202122;
  --text-muted: #54595d;
  --border: #a2a9b1;
  --border-soft: #c8ccd1;
  --border-accent: #a7d7f9;
  --panel-bg: #f8f9fa;
  --shade: #eaecf0;
  --link: #3366cc;
  --link-visited: #795cb2;
  --link-new: #d73333;
  --link-external: #3366cc;
  --selection: #cfe4ff;
  --serif: "Linux Libertine", "Georgia", "Times New Roman", Times, serif;
  --sans: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
  --mono: "DejaVu Sans Mono", "SFMono-Regular", Menlo, Consolas, monospace;
}
html[data-theme="dark"] {
  --page-bg: #101418;
  --body-bg: #1b1f24;
  --text: #e8eaed;
  --text-muted: #a2a9b1;
  --border: #4a5058;
  --border-soft: #3a4048;
  --border-accent: #35526e;
  --panel-bg: #23272d;
  --shade: #2a2f36;
  --link: #7cb0ff;
  --link-visited: #b9a3e3;
  --link-new: #ff8a80;
  --selection: #2f4a6b;
}
@media (prefers-color-scheme: dark) {
  html:not([data-theme="light"]) {
    --page-bg: #101418; --body-bg: #1b1f24; --text: #e8eaed; --text-muted: #a2a9b1;
    --border: #4a5058; --border-soft: #3a4048; --border-accent: #35526e;
    --panel-bg: #23272d; --shade: #2a2f36; --link: #7cb0ff; --link-visited: #b9a3e3;
    --link-new: #ff8a80; --selection: #2f4a6b;
  }
}
* { box-sizing: border-box; }
html { -webkit-text-size-adjust: 100%; }
body {
  margin: 0; background: var(--page-bg); color: var(--text);
  font-family: var(--sans); font-size: 14px; line-height: 1.6;
}
::selection { background: var(--selection); }
#mw-page-base {
  height: 5em; background: var(--body-bg);
  background-image: linear-gradient(to bottom, var(--body-bg) 50%, var(--page-bg) 100%);
  position: absolute; top: 0; left: 0; right: 0; z-index: 0;
}
.layout { position: relative; z-index: 1; display: flex; align-items: flex-start; gap: 0; }

/* ---------- sidebar ---------- */
.sidebar { flex: 0 0 11.5em; padding: 0.6em 0.8em 2em 0.8em; font-size: 0.875em; }
#p-logo { display: block; text-align: center; margin: 0.4em 0 0.2em; }
#p-logo img { width: 90px; height: 90px; }
.site-name { text-align: center; font-family: var(--serif); font-size: 1.15em; margin-bottom: 1.4em; }
.site-name a { color: var(--text); text-decoration: none; }
.portal { margin: 0 0 1.2em; }
.portal h3 {
  font-size: 0.86em; font-weight: normal; color: var(--text-muted);
  margin: 0 0 0.35em; padding-bottom: 0.2em; border-bottom: 1px solid var(--border-soft);
  text-transform: none;
}
.portal ul { list-style: none; margin: 0; padding: 0; }
.portal li { margin: 0.25em 0; line-height: 1.4; }
.portal .subnav { margin: 0.2em 0 0.4em 0.9em; border-left: 1px solid var(--border-soft); padding-left: 0.6em; }
.portal li.active > a { font-weight: bold; color: var(--text); }

/* ---------- head ---------- */
.content-column { flex: 1 1 auto; min-width: 0; }
#mw-head { display: flex; align-items: center; justify-content: flex-end; gap: 0.5em; padding: 0.55em 1em 0 0; min-height: 2.6em; }
.menu-toggle { display: none; }
.search { position: relative; display: flex; gap: 0.35em; }
.search input[type="search"] {
  width: 13.2em; max-width: 42vw; padding: 0.35em 0.5em; font: inherit; font-size: 0.9em;
  color: var(--text); background: var(--body-bg);
  border: 1px solid var(--border-soft); border-radius: 2px;
}
.search input[type="search"]:focus { outline: 2px solid var(--link); outline-offset: -1px; border-color: var(--link); }
.search button {
  padding: 0.35em 0.7em; font: inherit; font-size: 0.9em; cursor: pointer;
  color: var(--text); background: var(--panel-bg);
  border: 1px solid var(--border-soft); border-radius: 2px;
}
.search button:hover { background: var(--shade); }
.search-results {
  position: absolute; top: 100%; right: 0; z-index: 20; margin: 2px 0 0; padding: 0;
  list-style: none; width: 26em; max-width: 88vw; max-height: 60vh; overflow-y: auto;
  background: var(--body-bg); border: 1px solid var(--border); border-radius: 2px;
  box-shadow: 0 3px 9px rgba(0,0,0,0.18);
}
.search-results li { border-bottom: 1px solid var(--shade); }
.search-results li:last-child { border-bottom: 0; }
.search-results a { display: block; padding: 0.45em 0.6em; text-decoration: none; color: var(--text); }
.search-results a:hover, .search-results li.active a { background: var(--panel-bg); }
.search-results .r-title { color: var(--link); font-weight: bold; }
.search-results .r-path, .search-results .r-snippet { display: block; color: var(--text-muted); font-size: 0.85em; }
.search-results .r-snippet mark { background: #fc3; color: #000; }
.search-results .r-empty { padding: 0.6em; color: var(--text-muted); }

/* ---------- tabs ---------- */
#left-navigation, #right-navigation { display: inline-block; vertical-align: bottom; }
#right-navigation { float: right; }
.tabs { list-style: none; margin: 0; padding: 0 0 0 1em; display: flex; gap: 1px; align-items: flex-end; }
#right-navigation .tabs { padding: 0 1em 0 0; }
.tabs li {
  background: var(--panel-bg); border: 1px solid var(--border-accent); border-bottom: none;
  border-radius: 3px 3px 0 0; font-size: 0.8125em; line-height: 1.4;
}
.tabs li > a, .tabs li > span { display: block; padding: 0.45em 0.85em 0.35em; color: var(--link); text-decoration: none; }
.tabs li.selected { background: var(--body-bg); border-bottom: 1px solid var(--body-bg); margin-bottom: -1px; }
.tabs li.selected > span { color: var(--text); }
.tabs li:hover:not(.selected) { background: var(--shade); }

/* ---------- body ---------- */
.mw-body {
  clear: both; background: var(--body-bg);
  border: 1px solid var(--border-accent); border-right-width: 0;
  padding: 1.1em 1.6em 1.6em; margin-right: 0;
}
.firstHeading {
  font-family: var(--serif); font-weight: normal; font-size: 1.85em; line-height: 1.3;
  margin: 0 0 0.15em; padding-bottom: 0.2em; border-bottom: 1px solid var(--border);
}
#siteSub { font-size: 0.85em; color: var(--text-muted); margin-bottom: 0.6em; }
.breadcrumbs { font-size: 0.85em; color: var(--text-muted); margin: -0.2em 0 1em; }
.crumb-sep { color: var(--border); }
.mw-parser-output { max-width: 60em; }
.mw-parser-output > *:first-child { margin-top: 0; }
a { color: var(--link); text-decoration: none; }
a:visited { color: var(--link-visited); }
a:hover { text-decoration: underline; }
a:focus-visible, button:focus-visible, summary:focus-visible { outline: 2px solid var(--link); outline-offset: 2px; }
a.new, a.new:visited { color: var(--link-new); }
a.external::after {
  content: ""; display: inline-block; width: 0.75em; height: 0.75em; margin-left: 0.25em;
  background: currentColor; opacity: 0.55; vertical-align: baseline;
  -webkit-mask: var(--ext) no-repeat center / contain; mask: var(--ext) no-repeat center / contain;
  --ext: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 12 12"><path d="M6 1h5v5H9.5V3.5L5 8 4 7l4.5-4.5H6zM2 2h3v1.5H3.5v5h5V7H10v3H2z"/></svg>');
}
h1, h2, h3, h4, h5, h6 { font-weight: bold; line-height: 1.3; margin: 1.4em 0 0.4em; }
.mw-parser-output h1, .mw-parser-output h2 {
  font-family: var(--serif); font-weight: normal;
  border-bottom: 1px solid var(--border); padding-bottom: 0.17em;
}
.mw-parser-output h1 { font-size: 1.7em; }
.mw-parser-output h2 { font-size: 1.5em; }
.mw-parser-output h3 { font-size: 1.2em; }
.mw-parser-output h4 { font-size: 1.05em; }
.mw-parser-output h5, .mw-parser-output h6 { font-size: 1em; }
.heading-anchor {
  margin-left: 0.4em; font-size: 0.7em; opacity: 0; text-decoration: none;
  vertical-align: middle; transition: opacity 0.12s ease-in;
}
h1:hover .heading-anchor, h2:hover .heading-anchor, h3:hover .heading-anchor,
h4:hover .heading-anchor, .heading-anchor:focus { opacity: 0.6; }
p { margin: 0.55em 0 0.85em; }
ul, ol { margin: 0.35em 0 0.9em 1.6em; padding: 0; }
li { margin-bottom: 0.15em; }
li.task-list-item, li:has(> .task-checkbox) { list-style: none; margin-left: -1.35em; }
.task-checkbox { margin-right: 0.35em; vertical-align: -0.06em; }
dl { margin: 0.4em 0 0.9em; }
dt { font-weight: bold; }
dd { margin: 0 0 0.4em 1.6em; }
hr { height: 1px; border: 0; background: var(--border-soft); margin: 1.4em 0; }
blockquote {
  margin: 0.9em 0; padding: 0.4em 1em; border-left: 4px solid var(--shade);
  color: var(--text-muted);
}
blockquote p:first-child { margin-top: 0; }
blockquote p:last-child { margin-bottom: 0; }
code, kbd, samp { font-family: var(--mono); font-size: 0.9em; }
:not(pre) > code {
  background: var(--panel-bg); border: 1px solid var(--border-soft);
  border-radius: 2px; padding: 0.06em 0.35em; color: #b32d2e;
}
html[data-theme="dark"] :not(pre) > code { color: #ffb4a8; }
pre {
  background: var(--panel-bg); border: 1px solid var(--border-soft); border-radius: 2px;
  padding: 0.8em 1em; margin: 0.9em 0; overflow-x: auto; line-height: 1.45;
  font-family: var(--mono); font-size: 0.86em; tab-size: 4;
}
pre code { background: none; border: 0; padding: 0; color: inherit; font-size: 1em; }
img { max-width: 100%; height: auto; }
.mw-parser-output figure { margin: 0.9em 0; }
.mw-parser-output figcaption { font-size: 0.88em; color: var(--text-muted); }

/* ---------- tables ---------- */
table { border-collapse: collapse; margin: 0.9em 0; max-width: 100%; }
.mw-parser-output table:not(.wikitable):not(.infobox) th,
.mw-parser-output table:not(.wikitable):not(.infobox) td { padding: 0.3em 0.6em; }
table.wikitable {
  background: var(--body-bg); border: 1px solid var(--border);
  color: var(--text); font-size: 0.95em;
}
table.wikitable > * > tr > th, table.wikitable > * > tr > td {
  border: 1px solid var(--border-soft); padding: 0.35em 0.7em;
}
table.wikitable > * > tr > th { background: var(--shade); text-align: center; font-weight: bold; }
table.wikitable caption { font-weight: bold; padding-bottom: 0.3em; }
.mw-parser-output .infobox {
  float: right; clear: right; width: 22em; max-width: 90%; margin: 0 0 1em 1.4em;
  background: var(--panel-bg); border: 1px solid var(--border-soft); font-size: 0.88em;
}
.mw-parser-output .infobox th, .mw-parser-output .infobox td {
  border-bottom: 1px solid var(--shade); padding: 0.3em 0.6em; text-align: left; vertical-align: top;
}
.table-scroll { overflow-x: auto; }

/* ---------- contents box ---------- */
.toc {
  display: table; background: var(--panel-bg); border: 1px solid var(--border-soft);
  border-radius: 2px; padding: 0.6em 1.1em 0.7em 0.7em; margin: 1em 0 1.2em;
  font-size: 0.95em;
}
.toctitle { display: flex; align-items: baseline; gap: 0.5em; text-align: center; }
.toctitle h2 {
  display: inline; font-family: var(--serif); font-size: 1.05em; font-weight: bold;
  border: 0; margin: 0; padding: 0;
}
.toctogglespan { font-size: 0.85em; color: var(--text-muted); }
.toctogglebutton {
  background: none; border: 0; padding: 0; font: inherit; color: var(--link); cursor: pointer;
}
.toc ul { list-style: none; margin: 0.3em 0 0 0; padding: 0; }
.toc ul ul { margin-left: 1.4em; }
.toc li { margin: 0.15em 0; }
.toc .tocnumber { color: var(--text-muted); padding-right: 0.35em; }
.toc.collapsed .toc-list { display: none; }

/* ---------- generated list pages ---------- */
.page-list { list-style: none; margin-left: 0; }
.page-list li { padding-left: 1em; text-indent: -1em; }
.page-list li::before { content: "\\2022"; color: var(--border); padding-right: 0.5em; }
.page-list.columns { columns: 3 15em; column-gap: 2em; }
.page-blurb { color: var(--text-muted); font-size: 0.92em; }
.letter-nav {
  background: var(--panel-bg); border: 1px solid var(--border-soft); border-radius: 2px;
  padding: 0.5em 0.7em; margin: 0.8em 0 1.2em; line-height: 2;
}
.letter-nav a { display: inline-block; min-width: 1.6em; text-align: center; }
.mainpage-banner {
  background: var(--panel-bg); border: 1px solid var(--border-accent); border-radius: 2px;
  padding: 0.9em 1.2em; margin-bottom: 1.2em;
}
.mainpage-banner h2 { margin-top: 0.1em; border: 0; font-family: var(--serif); font-weight: normal; }
.mainpage-columns { display: grid; grid-template-columns: repeat(auto-fit, minmax(18em, 1fr)); gap: 1.2em; }
.mainpage-box { background: var(--body-bg); border: 1px solid var(--border-soft); border-radius: 2px; padding: 0.4em 1.1em 1em; }
.mainpage-box h2 { margin-top: 0.6em; font-size: 1.25em; }
.mainpage-footnote { color: var(--text-muted); margin-top: 1.4em; }
.empty { color: var(--text-muted); font-style: italic; }

/* ---------- footer areas ---------- */
.catlinks {
  clear: both; margin: 1.6em 0 0; padding: 0.45em 0.7em;
  background: var(--panel-bg); border: 1px solid var(--border-soft); border-radius: 2px;
  font-size: 0.9em;
}
.catlinks ul { display: inline; list-style: none; margin: 0; padding: 0; }
.catlinks li { display: inline-block; margin: 0; padding: 0 0.6em; border-left: 1px solid var(--border-soft); }
.catlinks li:first-child { border-left: 0; padding-left: 0.3em; }
.catlinks-label { font-weight: bold; }
.whatlinkshere {
  clear: both; margin: 1em 0 0; padding: 0.4em 0.7em; font-size: 0.9em;
  background: var(--panel-bg); border: 1px solid var(--border-soft); border-radius: 2px;
}
.whatlinkshere summary { cursor: pointer; color: var(--link); }
.whatlinkshere ul { margin-top: 0.5em; }
.printfooter { display: none; }
#footer {
  clear: both; margin: 0 0 2em; padding: 0.8em 1.6em 1em;
  border-top: 1px solid var(--border-soft);
  color: var(--text-muted); font-size: 0.8125em;
}
#footer p { margin: 0.3em 0; }
.footer-links { list-style: none; margin: 0.4em 0 0; padding: 0; }
.footer-links li { display: inline-block; margin-right: 1.2em; }
.visually-hidden {
  position: absolute !important; width: 1px; height: 1px; margin: -1px;
  overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap;
}
.skip-link:focus {
  position: static !important; width: auto; height: auto; margin: 0; clip: auto;
  display: inline-block; padding: 0.4em 0.8em; background: var(--body-bg);
}

/* ---------- responsive ---------- */
@media (max-width: 900px) {
  .layout { display: block; }
  .sidebar {
    display: none; width: auto; padding: 0.8em 1em;
    background: var(--panel-bg); border-bottom: 1px solid var(--border-soft);
  }
  body.nav-open .sidebar { display: block; }
  #p-logo img { width: 56px; height: 56px; }
  .site-name { margin-bottom: 0.8em; }
  #mw-head { justify-content: space-between; padding: 0.5em 0.8em 0; }
  .menu-toggle {
    display: inline-block; font-size: 1.3em; line-height: 1; padding: 0.2em 0.5em;
    color: var(--text); background: var(--panel-bg);
    border: 1px solid var(--border-soft); border-radius: 2px; cursor: pointer;
  }
  .mw-body { border-left: 0; border-right: 0; padding: 0.9em 1em 1.2em; }
  #left-navigation, #right-navigation { float: none; display: block; }
  #right-navigation .tabs { padding-left: 1em; }
  .page-list.columns { columns: 1; }
  #footer { padding: 0.8em 1em; }
}
@media print {
  #mw-page-base, .sidebar, #mw-head, #left-navigation, #right-navigation,
  .toctogglespan, .heading-anchor, .whatlinkshere, .footer-links, .skip-link { display: none !important; }
  body { background: #fff; font-size: 11pt; }
  .mw-body { border: 0; padding: 0; }
  .printfooter { display: block; margin-top: 1.5em; color: #555; font-size: 0.85em; }
  a { color: #000; text-decoration: underline; }
  pre, blockquote, table { break-inside: avoid; }
}
@media (prefers-reduced-motion: reduce) {
  * { transition: none !important; animation: none !important; }
}
"""

SCRIPT = r"""/* mdwiki - client-side search, theme toggle, small niceties. No dependencies, file:// safe. */
(function () {
  "use strict";
  var body = document.body;
  var base = body.getAttribute("data-base") || "";
  var index = window.MDWIKI_INDEX || [];
  var currentPage = body.getAttribute("data-page") || "";

  /* ---- storage (localStorage can throw on file:// in some browsers) ---- */
  function readPref(key) {
    try { return window.localStorage.getItem(key); } catch (e) { return null; }
  }
  function writePref(key, value) {
    try { window.localStorage.setItem(key, value); } catch (e) { /* ignore */ }
  }

  /* ---- theme ---- */
  var saved = readPref("mdwiki-theme");
  if (saved === "dark" || saved === "light") {
    document.documentElement.setAttribute("data-theme", saved);
  }
  function toggleTheme() {
    var root = document.documentElement;
    var explicit = root.getAttribute("data-theme");
    var dark = explicit
      ? explicit === "dark"
      : window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
    var next = dark ? "light" : "dark";
    root.setAttribute("data-theme", next);
    writePref("mdwiki-theme", next);
  }

  /* ---- search ---- */
  var input = document.getElementById("searchInput");
  var results = document.getElementById("searchResults");
  var active = -1;

  function escapeHtml(text) {
    return String(text).replace(/[&<>"']/g, function (ch) {
      return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[ch];
    });
  }

  function score(record, terms) {
    var title = record.t.toLowerCase();
    var path = record.u.toLowerCase();
    var headings = (record.h || []).join(" ").toLowerCase();
    var text = ((record.x || "") + " " + (record.c || []).join(" ")).toLowerCase();
    var total = 0;
    for (var i = 0; i < terms.length; i++) {
      var term = terms[i];
      var hit = 0;
      if (title === term) hit += 120;
      if (title.indexOf(term) === 0) hit += 60;
      if (title.indexOf(term) > -1) hit += 40;
      if (headings.indexOf(term) > -1) hit += 12;
      if (path.indexOf(term) > -1) hit += 8;
      if (text.indexOf(term) > -1) hit += 5;
      if (!hit) return 0;
      total += hit;
    }
    return total;
  }

  function snippet(record, terms) {
    var text = record.x || record.s || "";
    var lower = text.toLowerCase();
    var at = -1;
    for (var i = 0; i < terms.length && at < 0; i++) at = lower.indexOf(terms[i]);
    var start = at > 60 ? at - 60 : 0;
    var piece = text.slice(start, start + 160);
    if (start > 0) piece = "\u2026" + piece;
    if (start + 160 < text.length) piece += "\u2026";
    var markup = escapeHtml(piece);
    terms.forEach(function (term) {
      if (!term) return;
      var safe = term.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
      markup = markup.replace(new RegExp("(" + safe + ")", "gi"), "<mark>$1</mark>");
    });
    return markup;
  }

  function search(query) {
    var terms = query.toLowerCase().split(/\s+/).filter(Boolean);
    if (!terms.length) return [];
    var found = [];
    for (var i = 0; i < index.length; i++) {
      var value = score(index[i], terms);
      if (value > 0) found.push({ record: index[i], value: value });
    }
    found.sort(function (a, b) {
      return b.value - a.value || a.record.t.localeCompare(b.record.t);
    });
    return found.slice(0, 12).map(function (entry) {
      return { record: entry.record, snippet: snippet(entry.record, terms) };
    });
  }

  function hide() {
    if (!results) return;
    results.hidden = true;
    results.innerHTML = "";
    active = -1;
    if (input) input.setAttribute("aria-expanded", "false");
  }

  function render(query) {
    if (!results) return;
    var matches = search(query);
    if (!query.trim()) return hide();
    if (!matches.length) {
      results.innerHTML = '<li class="r-empty">No pages match &ldquo;' + escapeHtml(query) + '&rdquo;.</li>';
      results.hidden = false;
      if (input) input.setAttribute("aria-expanded", "true");
      return;
    }
    results.innerHTML = matches.map(function (match, n) {
      var href = base + match.record.u.split("/").map(encodeURIComponent).join("/");
      return '<li role="option" data-n="' + n + '"><a href="' + escapeHtml(href) + '">' +
        '<span class="r-title">' + escapeHtml(match.record.t) + "</span>" +
        '<span class="r-path">' + escapeHtml(match.record.u) + "</span>" +
        '<span class="r-snippet">' + match.snippet + "</span></a></li>";
    }).join("");
    results.hidden = false;
    active = -1;
    if (input) input.setAttribute("aria-expanded", "true");
  }

  function move(step) {
    if (!results || results.hidden) return;
    var items = results.querySelectorAll("li[data-n]");
    if (!items.length) return;
    if (active > -1) items[active].classList.remove("active");
    active = (active + step + items.length) % items.length;
    items[active].classList.add("active");
    items[active].scrollIntoView({ block: "nearest" });
  }

  if (input) {
    var timer = null;
    input.addEventListener("input", function () {
      window.clearTimeout(timer);
      var value = input.value;
      timer = window.setTimeout(function () { render(value); }, 90);
    });
    input.addEventListener("keydown", function (event) {
      if (event.key === "ArrowDown") { event.preventDefault(); move(1); }
      else if (event.key === "ArrowUp") { event.preventDefault(); move(-1); }
      else if (event.key === "Enter") {
        var items = results ? results.querySelectorAll("li[data-n] a") : [];
        var target = items[active > -1 ? active : 0];
        if (target) { event.preventDefault(); window.location.href = target.getAttribute("href"); }
      } else if (event.key === "Escape") { hide(); input.blur(); }
    });
    document.addEventListener("click", function (event) {
      if (!event.target.closest || !event.target.closest("#p-search")) hide();
    });
    document.addEventListener("keydown", function (event) {
      var typing = /^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement.tagName);
      if ((event.key === "/" && !typing) || (event.key.toLowerCase() === "k" && (event.ctrlKey || event.metaKey))) {
        event.preventDefault();
        input.focus();
        input.select();
      }
    });
  }

  /* ---- actions ---- */
  function randomPage() {
    var options = index.filter(function (record) { return record.u !== currentPage; });
    if (!options.length) options = index;
    if (!options.length) return;
    var pick = options[Math.floor(Math.random() * options.length)];
    window.location.href = base + pick.u.split("/").map(encodeURIComponent).join("/");
  }

  document.addEventListener("click", function (event) {
    var trigger = event.target.closest ? event.target.closest("[data-action]") : null;
    if (!trigger) return;
    var action = trigger.getAttribute("data-action");
    if (action === "theme") { event.preventDefault(); toggleTheme(); }
    else if (action === "random") { event.preventDefault(); randomPage(); }
    else if (action === "print") { event.preventDefault(); window.print(); }
    else if (action === "menu") { event.preventDefault(); body.classList.toggle("nav-open"); }
    else if (action === "search") { event.preventDefault(); if (input) { render(input.value); input.focus(); } }
    else if (action === "toggle-toc") {
      event.preventDefault();
      var toc = document.getElementById("toc");
      if (!toc) return;
      var collapsed = toc.classList.toggle("collapsed");
      trigger.textContent = collapsed ? "show" : "hide";
      trigger.setAttribute("aria-expanded", collapsed ? "false" : "true");
      writePref("mdwiki-toc", collapsed ? "collapsed" : "open");
    }
  });

  var toc = document.getElementById("toc");
  if (toc && readPref("mdwiki-toc") === "collapsed") {
    toc.classList.add("collapsed");
    var button = toc.querySelector(".toctogglebutton");
    if (button) { button.textContent = "show"; button.setAttribute("aria-expanded", "false"); }
  }

  /* ---- task lists lose their bullet (fallback for browsers without :has) ---- */
  var checkboxes = document.querySelectorAll(".mw-parser-output li > .task-checkbox");
  Array.prototype.forEach.call(checkboxes, function (box) {
    box.parentNode.classList.add("task-list-item");
  });

  /* ---- wide tables get a horizontal scroller ---- */
  var tables = document.querySelectorAll(".mw-parser-output table");
  Array.prototype.forEach.call(tables, function (table) {
    if (table.closest(".table-scroll")) return;
    var wrap = document.createElement("div");
    wrap.className = "table-scroll";
    table.parentNode.insertBefore(wrap, table);
    wrap.appendChild(table);
  });
})();
"""


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="mdwiki",
        description="Turn a folder of Markdown files into a static, Wikipedia-styled HTML site "
                    "that works straight from the filesystem.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="examples:\n"
               "  python3 mdwiki.py ./notes\n"
               "  python3 mdwiki.py ./notes -o ./public --site-name 'Team Handbook' --clean\n",
    )
    parser.add_argument("input", nargs="?", default=".", type=Path,
                        help="folder to read Markdown from (default: current folder)")
    parser.add_argument("-o", "--output", default=Path("./outputs"), type=Path,
                        help="folder to write the site into (default: ./outputs)")
    parser.add_argument("--site-name", default=None, help="wiki name shown in the sidebar and titles")
    parser.add_argument("--tagline", default=None, help="text under each page title")
    parser.add_argument("--lang", default="en", help="value for the html lang attribute (default: en)")
    parser.add_argument("--theme", choices=["auto", "light", "dark"], default="auto",
                        help="default colour theme; 'auto' follows the operating system (default: auto)")
    parser.add_argument("--engine", choices=["auto", "markdown", "builtin"], default="auto",
                        help="Markdown renderer: the `markdown` package if available, or the built-in one")
    parser.add_argument("--clean", action="store_true", help="delete the output folder before writing")
    parser.add_argument("--dry-run", action="store_true", help="parse and report, but write nothing")
    parser.add_argument("--include-hidden", action="store_true",
                        help="also include dot-files and dot-folders")
    parser.add_argument("--no-source", dest="copy_source", action="store_false",
                        help="do not copy .md sources next to the pages (drops the 'View source' tab)")
    parser.add_argument("--no-backlinks", action="store_true",
                        help="omit the 'Pages that link here' box")
    parser.add_argument("--no-toc", action="store_true", help="never render a contents box")
    parser.add_argument("--toc-min", type=int, default=3, metavar="N",
                        help="minimum headings before a contents box appears (default: 3)")
    parser.add_argument("--toc-depth", type=int, default=3, metavar="N",
                        help="heading depth shown in the contents box (default: 3)")
    parser.add_argument("--index-chars", type=int, default=1200, metavar="N",
                        help="characters of each page kept in the search index (default: 1200)")
    parser.add_argument("--max-warnings", type=int, default=15, metavar="N",
                        help="unresolved links to list at the end of a build (default: 15)")
    parser.add_argument("-q", "--quiet", action="store_true", help="print nothing but errors")
    parser.add_argument("-v", "--verbose", action="store_true", help="print extra build detail")
    parser.add_argument("--version", action="version", version=f"mdwiki {__version__}")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.site_name is None:
        resolved = args.input.resolve()
        args.site_name = humanize(resolved.name or "Wiki")
    if args.tagline is None:
        args.tagline = f"From {args.site_name}, a wiki built from Markdown"
    args.toc_min = max(1, args.toc_min)
    args.toc_depth = min(max(1, args.toc_depth), 6)

    try:
        SiteBuilder(args).build()
    except SystemExit:
        raise
    except KeyboardInterrupt:
        print("\ninterrupted", file=sys.stderr)
        return 130
    return 0


if __name__ == "__main__":
    sys.exit(main())
