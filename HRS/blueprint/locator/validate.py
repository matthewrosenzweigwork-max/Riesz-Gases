from pathlib import Path as P
from lxml import html
import argparse,csv,collections,hashlib,json,re
from urllib.parse import urlsplit,unquote
a=argparse.ArgumentParser();a.add_argument('hrs',type=P);a.add_argument('--out',type=P,required=True);arg=a.parse_args();H=arg.hrs.resolve();C=H/'coverage'
def tsv(f):return list(csv.DictReader(f.open(),delimiter='\t'))
files=sorted(C.rglob('*.html')); ids={};links=[]; targets=[]; claims=[];actual={}; section=[]; math=0;srcfiles={}
for f in files:
 d=html.fromstring(f.read_bytes().decode())
 isrc=f.parent.name=='source';isec=f.parent.name=='sections'
 idlist=d.xpath('//@id'); assert len(set(idlist))==len(idlist),(f.name,'duplicate anchors')
 ids[f]=set(idlist)
 assert len(d.xpath('//main'))==1 and d.xpath('string(/html/@lang)')=='en'
 assert not d.xpath('//script|//iframe|//img|//*[@onload]|//*[@onclick]|//style')
 assert not re.search(r'(?:/(?:home|Users|workspace)/[\w.-]+/|/data/[\w.-]+/|file://|token_[A-Za-z0-9]{15})',d.xpath('string(//main)')),(f,'unintended private path')
 if isrc:
  rel=f.stem.replace('.','/')+'.lean';src=H/'lean'/rel
  if not src.is_file():src=C/'checks'/rel;assert (H/'proof-supplement'/rel).read_bytes()==src.read_bytes()
  ls=src.read_text().splitlines();source=d.xpath('//pre/code/span[@class="line"]');assert len(ls)==len(source) and source
  # Compare the full code on every line directly with the Lean source, excluding the generated line-number glyph.
  for i,(line,el) in enumerate(zip(ls,source),1):assert (el.get('id')=='L'+str(i) and (el[0].tail or '').removesuffix('\n')==line),(f.name,i)
  srcfiles[f.stem]=hashlib.sha256(src.read_bytes()).hexdigest()
 for r in d.xpath('//article[@data-paper-id]'):
  targets.append(r.get('data-paper-id')); 
  for li in r.xpath('.//*[@data-ledger-line]'): claims.append(int(li.get('data-ledger-line')))
 if isec:
  for t in d.xpath('//h2[@id]'):section.append(t.get('id'))
  math+=len(d.xpath('//math'));assert all(el.xpath('string(.//annotation)') for el in d.xpath('//math'))
 for href in d.xpath('//a/@href | //link/@href'):
  if href.startswith('#L') and isrc:assert href[1:]in ids[f];continue
  links.append((f,href))
for f,v in links:
 u=urlsplit(v);assert not u.netloc and not u.scheme,(f,v);p=(f.parent/unquote(u.path)).resolve() if u.path else f
 assert p.is_relative_to(H) and p.exists(),(f,v,p)
 if p.is_dir():p=p/'index.html'
 if u.fragment:
  assert p in ids and unquote(u.fragment) in ids[p],(f,v)
assert len(targets)==len(set(targets))==334 and len(section)==len(set(section))==143
expected_lines=[line for line in range(2,1184) if line!=740]
assert sorted(claims)==expected_lines, (len(claims),sorted(set(expected_lines)-set(claims))[:22])
# The removed D.6 card survives only as a neutral historical anchor in Appendix D.
legacy_id='p-'+hashlib.sha256(b'M:B:lem:fdl-commutator').hexdigest()[:14]
legacy=html.fromstring((C/'sections/M-D.html').read_bytes()).xpath('//*[@id=$id]',id=legacy_id)
assert len(legacy)==1 and legacy[0].tag=='span' and not legacy[0].text_content().strip()
assert 'M:B:lem:fdl-commutator' not in targets
assert 740 not in claims
assert len([p for p in files if p.parent.name=='sections'])==24
out={'status':'PASS','html_pages':len(files),'paper_targets':len(targets),'neutral_historical_anchors':1,'excluded_historical_ledger_line':740,'claim_rows':len(claims),'distinct_sections':24,'subsections':len(section),'numbered_lean_source_files_checked':len(srcfiles),'all_source_lines_exact':True,'math_instances':math,'hrefs_checked_excluding_source_self_line_links':len(links),'all_hrefs_and_anchors_valid':True,'public_path_scan_clean':True,'strict_local_links':True}
arg.out.write_text(json.dumps(out,indent=2)+'\n');print(out)
