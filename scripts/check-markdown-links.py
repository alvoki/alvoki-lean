#!/usr/bin/env python3
"""Check local Markdown links without downloading external resources."""
import html
import re
import subprocess
import sys
import unicodedata
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
FENCE = re.compile(r'^ {0,3}(`{3,}|~{3,})')
REF = re.compile(r'^ {0,3}\[([^]]+)\]:\s*(?:<([^>]+)>|(\S+))', re.M)
HTML_ID = re.compile(r'<[A-Za-z][^>]*\b(?:id|name)\s*=\s*["\']([^"\']+)["\']', re.I)
INLINE_CODE = re.compile(r'(`+)(.*?)(?<!`)\1(?!`)', re.S)


def visible(text):
    """Mask fences, comments, and inline code while retaining line breaks."""
    text = re.sub(r'<!--.*?-->', lambda m: re.sub(r'[^\n]', ' ', m.group()), text, flags=re.S)
    lines, fence = [], None
    list_indent = None
    paragraph = False
    indented_code = False
    for line in text.splitlines(keepends=True):
        match = FENCE.match(line)
        expanded = line.expandtabs(4)
        indent = len(expanded) - len(expanded.lstrip(' '))
        item = re.match(r'^( *)(?:[-+*]|\d{1,9}[.)]) +', expanded)
        if item:
            list_indent = item.end()
            indented_code = False
            paragraph = True
        elif line.strip() and indent == 0:
            list_indent = None
        code_indent = (list_indent or 0) + 4
        if fence:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence):
                fence = None
            lines.append(re.sub(r'[^\n]', ' ', line))
        elif match:
            fence = match[1]
            indented_code = False
            paragraph = False
            lines.append(re.sub(r'[^\n]', ' ', line))
        elif line.strip() and not item and indent >= code_indent and (indented_code or not paragraph):
            indented_code = True
            lines.append(re.sub(r'[^\n]', ' ', line))
        elif not line.strip():
            paragraph = False
            lines.append(line)
        else:
            indented_code = False
            paragraph = True
            lines.append(line)
    return ''.join(lines)


def normalized(label):
    return ' '.join(label.split()).casefold()


def anchors(text):
    text = visible(text)
    result = set(HTML_ID.findall(text))
    counts = {}
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r'^ {0,3}#{1,6}\s+(.*?)(?:\s+#+\s*)?$', line)
        if m:
            heading = m[1]
        elif i + 1 < len(lines) and re.match(r'^ {0,3}(?:=+|-+)\s*$', lines[i + 1]) and line.strip():
            heading = line.strip()
        else:
            continue
        heading = re.sub(r'<[^>]*>', '', heading)
        heading = re.sub(r'!?\[([^]]+)\]\([^)]*\)', r'\1', heading)
        heading = html.unescape(heading).lower().replace('`', '')
        slug = ''.join(c for c in heading if c in '-_' or c.isspace() or unicodedata.category(c)[0] in 'LN M'.replace(' ', ''))
        slug = slug.replace(' ', '-')
        count = counts.get(slug, 0)
        counts[slug] = count + 1
        result.add(slug if not count else f'{slug}-{count}')
    return result


def links(text):
    text = visible(text)
    refs = {normalized(m[1]): m[2] or m[3] for m in REF.finditer(text)}
    text = REF.sub(lambda m: ' ' * len(m.group()), text)
    text = INLINE_CODE.sub(lambda m: re.sub(r'[^\n]', ' ', m.group()), text)
    # Explicit links, images, and full/collapsed reference links. Balanced
    # parentheses in destinations are accepted; angle brackets allow spaces.
    pattern = re.compile(r'!?\[((?:\\.|[^\[\]\\]|\[[^\[\]]*\])*)\][ \t]*(?:\((<[^>]*>|(?:\\.|[^()\s]|\([^()]*\))*)(?:\s+["\'][^"\']*["\'])?\)|\[([^]]*)\])')
    occupied = []
    for m in pattern.finditer(text):
        occupied.append(m.span())
        target = m[2]
        if target is None:
            label = normalized(m[3] or m[1])
            if label not in refs:
                yield m.start(), None, f'undefined reference [{label}]'
                continue
            target = refs[label]
        yield m.start(), target.strip('<>'), None
    # A shortcut reference is a link only when its definition exists.
    for m in re.finditer(r'!?\[([^]\n]+)\]', text):
        if any(start <= m.start() < end for start, end in occupied):
            continue
        label = normalized(m[1])
        if label in refs:
            yield m.start(), refs[label].strip('<>'), None
    for m in re.finditer(r'<(?:a|img)\b[^>]*?\b(?:href|src)\s*=\s*["\']([^"\']+)["\']', text, re.I):
        yield m.start(), m[1], None


def check(root, files):
    errors = []
    for file in files:
        text = file.read_text(encoding='utf-8')
        for pos, target, error in links(text):
            line = text.count('\n', 0, pos) + 1
            if error:
                errors.append((file, line, error)); continue
            target = html.unescape(re.sub(r'\\([!"#$%&\'()*+,\-./:;<=>?@\[\\\]^_`{|}~])', r'\1', target))
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc or target.startswith('/'):
                continue
            path = (file.parent / unquote(parsed.path)).resolve() if parsed.path else file.resolve()
            if not path.exists():
                errors.append((file, line, f'missing path: {target}')); continue
            if parsed.fragment and path.is_file() and path.suffix.lower() in ('.md', '.markdown'):
                if unquote(parsed.fragment) not in anchors(path.read_text(encoding='utf-8')):
                    errors.append((file, line, f'missing anchor: {target}'))
    return errors


def main():
    files = [ROOT / p for p in subprocess.check_output(['git', 'ls-files', '-z', '--', '*.md', '*.markdown'], cwd=ROOT).decode().split('\0') if p]
    errors = check(ROOT, files)
    for file, line, message in errors:
        print(f'{file.relative_to(ROOT)}:{line}: {message}', file=sys.stderr)
    print(f'Checked {len(files)} Markdown files; {len(errors)} error(s).')
    return bool(errors)


if __name__ == '__main__':
    sys.exit(main())
