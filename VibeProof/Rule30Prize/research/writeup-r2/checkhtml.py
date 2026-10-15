#!/usr/bin/env python3
import sys, re
from html.parser import HTMLParser
VOID = {'area','base','br','col','embed','hr','img','input','link','meta','source','track','wbr'}
class P(HTMLParser):
    def __init__(s):
        super().__init__(convert_charrefs=True); s.stack=[]; s.errs=[]; s.ids={}; s.hrefs=[]; s.ext=[]
    def handle_starttag(s, tag, attrs):
        a = dict(attrs)
        if 'id' in a:
            if a['id'] in s.ids: s.errs.append(f"duplicate id {a['id']}")
            s.ids[a['id']] = 1
        for k in ('href', 'src'):
            v = a.get(k)
            if v and k == 'href' and v.startswith('#'): s.hrefs.append(v[1:])
            elif v and (v.startswith('http') or v.startswith('//')): s.ext.append(v)
            elif v and k == 'src': s.ext.append(v)
        if tag not in VOID: s.stack.append((tag, s.getpos()))
    def handle_startendtag(s, tag, attrs):
        s.handle_starttag(tag, attrs)
        if tag not in VOID and s.stack and s.stack[-1][0] == tag: s.stack.pop()
    def handle_endtag(s, tag):
        if tag in VOID: return
        if not s.stack: s.errs.append(f'stray </{tag}> at {s.getpos()}'); return
        if s.stack[-1][0] != tag:
            # find in stack
            names = [t for t, _ in s.stack]
            if tag in names:
                while s.stack and s.stack[-1][0] != tag:
                    t, pos = s.stack.pop(); s.errs.append(f'unclosed <{t}> opened at {pos}, closed by </{tag}> at {s.getpos()}')
                s.stack.pop()
            else:
                s.errs.append(f'stray </{tag}> at {s.getpos()}')
        else: s.stack.pop()
p = P(); src = open(sys.argv[1], encoding='utf-8').read(); p.feed(src); p.close()
print('errors:', len(p.errs)); [print('  ', e) for e in p.errs[:20]]
print('unclosed at end:', [(t, pos) for t, pos in p.stack][:10])
missing = sorted(set(h for h in p.hrefs if h not in p.ids))
print('internal links:', len(p.hrefs), 'missing targets:', missing[:20])
print('external refs:', p.ext[:10])
print('http(s) strings in file:', len(re.findall(r'https?://', src)))
