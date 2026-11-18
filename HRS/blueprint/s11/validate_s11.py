#!/usr/bin/env python3
"""Validate the S11 overlay's local links, anchors, exact source spans and math."""
from pathlib import Path as P
import argparse,hashlib,json,re
from urllib.parse import urlsplit,unquote
from lxml import html as H
p=argparse.ArgumentParser();p.add_argument('--tree',type=P,required=True);p.add_argument('--report',type=P);a=p.parse_args();root=a.tree.resolve();here=root/'blueprint/s11';data=json.loads((here/'content.json').read_text());page=root/'reader/Relaxation-on-moving-windows/index.html';d=H.fromstring(page.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
expected=[]
for c in data['cards']:
 for key,lk in [('file','lines'),('provider_file','provider_lines')]:
  if key in c:
   lines=(root/c[key]).read_text().splitlines(keepends=True);i,j=c[lk];expected.append(''.join(lines[i-1:j]))
assert d.xpath('//pre/text()')==expected
expr=re.compile(r'\$\$(.*?)\$\$|(?<!\$)\$(?!\$)(.*?)\$(?!\$)',re.S)
mds=[data['introduction'],data['setting']]+[c['body'] for c in data['cards']];tex=[m[1] if m[1] is not None else m[2] for md in mds for m in expr.finditer(md)];assert d.xpath('//annotation/text()')==tex
labels=d.xpath('//*[contains(@class,"eq-number")]/text()');assert labels==[f'(S11.{i})' for i in range(1,len(labels)+1)]
files=[page,root/'reader/index.html',root/'reader/Browse-the-paper-and-supplement/index.html',root/'reader/Whole-space-fluctuations/index.html',root/'coverage/index.html',root/'coverage/sections/S-S11.html'];cache={};errors=[];count=0
for f in files:
 doc=H.fromstring(f.read_text());ids=doc.xpath('//*[@id]/@id');assert len(ids)==len(set(ids)),('duplicate ID',f)
 base=doc.xpath('//base/@href');directory=(f.parent/(base[0] if base else '.')).resolve()
 for ref in doc.xpath('//*[not(self::base)]/@href|//@src'):
  u=urlsplit(ref)
  if u.scheme or u.netloc:continue
  target=(directory/unquote(u.path)).resolve() if u.path else f
  if target.is_dir():target/='index.html'
  if not target.exists():errors.append([str(f.relative_to(root)),ref,'missing']);continue
  if u.fragment and target.suffix=='.html':
   if target not in cache:cache[target]=set(H.fromstring(target.read_text()).xpath('//*[@id]/@id'))
   if unquote(u.fragment) not in cache[target]:errors.append([str(f.relative_to(root)),ref,'fragment'])
  count+=1
assert not errors,errors
assert not d.xpath('//script|//iframe|//link')
for token in ['/data/','/home/','/workspace/','file://','reader-anchor:']:
 assert token not in page.read_text(),('private path',token)
# Distinct labels are mandatory on admitted declarations and companion proofs.
assert sum('Original Lean declaration (admitted)' in x for x in d.xpath('//summary/text()'))==2
assert sum('Companion proof (exact type checked)' in x for x in d.xpath('//summary/text()'))==2
r={'cards':len(data['cards']),'source_spans_exact':len(expected),'tex_spans_exact':len(tex),'display_labels':labels,'checked_local_refs':count,'link_errors':errors,'static_page_external_dependencies':0,'page_sha256':sha(page.read_bytes()),'content_sha256':sha((here/'content.json').read_bytes())}
if a.report:a.report.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
