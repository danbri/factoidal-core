#!/usr/bin/env python3
"""Turn a status note in Markdown into HTML that the Lean engine can render.

    tools/status-to-html.py SOURCE.md OUTPUT.html [--check]

Reads headings, paragraphs, `- ` lists and [text](url) links, and refuses any
other Markdown and any non-ASCII text, because the engine's default font is
ASCII. --check exits 1 when OUTPUT differs. The output has no script.
"""
import html, re, sys

STYLE = ('body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:white}'
         'main{width:640px}h1{margin:0;font-size:21px;line-height:28px;color:#184078}'
         'h2{margin:0;padding-top:14px;font-size:16px;line-height:24px;color:#184078}'
         'p{margin:0;padding-top:6px}')


def inline(text):
    parts = re.split(r'(\[[^\]]+\]\([^)]+\))', text)
    out = []
    for part in parts:
        link = re.fullmatch(r'\[([^\]]+)\]\(([^)]+)\)', part)
        if link:
            out.append(f'<a href="{html.escape(link[2])}">{html.escape(link[1])}</a>')
        else:
            if any(mark in part for mark in ('`', '*', '_', '[')):
                sys.exit(f'unsupported Markdown: {part}')
            out.append(html.escape(part, quote=False))
    return ''.join(out)


def convert(source):
    if not source.isascii():
        sys.exit('non-ASCII text: the engine default font is ASCII')
    text = re.sub(r'\A---\n.*?\n---\n', '', source, flags=re.S)
    body, title = [], 'Status'
    for block in re.split(r'\n\s*\n', text.strip()):
        lines = block.split('\n')
        if block.startswith('# '):
            title = block[2:]
            body.append(f'<h1>{inline(title)}</h1>')
        elif block.startswith('## '):
            body.append(f'<h2>{inline(block[3:])}</h2>')
        elif all(line.startswith('- ') for line in lines):
            body.extend(f'<p>- {inline(line[2:])}</p>' for line in lines)
        else:
            body.append(f'<p>{inline(" ".join(lines))}</p>')
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>{html.escape(title)}</title>'
            f'<style>{STYLE}</style></head><body><main>\n' + '\n'.join(body) + '\n</main></body></html>\n')


result = convert(open(sys.argv[1], encoding='utf-8').read())
if '--check' in sys.argv:
    sys.exit(0 if open(sys.argv[2], encoding='utf-8').read() == result else 1)
open(sys.argv[2], 'w', encoding='utf-8').write(result)
