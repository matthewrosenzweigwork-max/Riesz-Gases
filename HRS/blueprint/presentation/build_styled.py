#!/usr/bin/env python3
"""Rebuild new styled cards and assemble hash-locked, frozen baseline editorial assets."""
from pathlib import Path as P
import argparse,hashlib,json,re,shutil,subprocess,os,tempfile
from urllib.parse import urlsplit,unquote
from lxml import html as H,etree as E
p=argparse.ArgumentParser();p.add_argument('--tree',type=P,required=True);p.add_argument('--handoff',type=P);p.add_argument('--output',type=P,required=True);p.add_argument('--with-coverage',action='store_true');p.add_argument('--lean-manifest',type=P);a=p.parse_args()
a.lean_manifest=a.lean_manifest or a.tree/'lean/MANIFEST/SHA256SUMS_included_files.txt'
here=P(__file__).resolve().parent; lock=json.loads((here/'INPUTS.json').read_text()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,h in lock['presentation_inputs'].items():assert sha(here/rel)==h,('stale presentation input',rel)
for rel,h in lock['tree_inputs'].items():assert sha(a.tree/rel)==h,('stale candidate input',rel)
handoff=a.handoff or here/'native-handoff'
for rel,h in lock['handoff_inputs'].items():assert sha(handoff/rel)==h,('stale sanitized native handoff',rel)
native=json.loads((handoff/'manifest.json').read_text())
assert not a.output.exists(),'output must be a fresh directory'
a.output.mkdir(parents=True); out=a.output/'reader';shutil.copytree(here/'baseline',out);shutil.copytree(here/'notices',out/'notices')
a_cards=json.loads((here/'equilibrium-and-paths.json').read_text());b_cards=json.loads((here/'preparation-and-fields.json').read_text());cards=a_cards[:3]+b_cards+a_cards[3:];assert len(cards)==8
# Exact lexical correspondence to frozen Lean, including the displayed proof.
for c in cards:
 source=a.tree/'lean'/c['source_file'];s=source.read_text();assert c['exact_signature'] in s and c['exact_proof'] in s,c['name']
 dst=a.output/'lean'/c['source_file'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,dst)
with tempfile.TemporaryDirectory() as t:
 w=P(t)
 for f in ['equilibrium-and-paths.json','preparation-and-fields.json','conventions.md','katex.js']:shutil.copy2(here/f,w/f)
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1",HRS_HEADLINE_WORK=str(w),HRS_MATH_STYLE=str(here),HRS_READER_BASE=str(here/'compact-base.html'))
 subprocess.run(['python3',str(here/'render_headlines.py')],env=env,check=True,capture_output=True)
 full=H.fromstring((w/'HRS-whole-space-reading-copy.html').read_text());chapter=full.get_element_by_id('hrs-whole-space-headlines');head=full.find('head')
 # Ordered mathematical data comes only from the hash-locked sanitized native handoff.
 tex=lambda x: re.sub(r'\s+','',x)
 native_tex=native['ordered_tex']
 new_tex=[tex(x.text_content()) for x in chapter.xpath('.//annotation[@encoding="application/x-tex"]')]
 assert native_tex==new_tex,('ordered native TeX divergence',len(native_tex),len(new_tex))
 native_cards={x['id']:x for x in native['cards']};assert len(native_cards)==8
 ids=set(chapter.xpath('.//*[@id]/@id'));ids.add(chapter.get('id'))
 for c in cards:
  ident='headline-'+c['name'].split('.')[-1].replace('_','-');target=chapter.get_element_by_id(ident);binding=native_cards[ident]
  assert c['name']==binding['declaration'],('native declaration mismatch',c['name'])
  assert binding['ordered_tex']==[tex(x.text_content()) for x in target.xpath('.//annotation[@encoding="application/x-tex"]')],('per-card TeX divergence',c['name'])
  for alias in binding['aliases']:
   if alias not in ids:target.insert(0,E.Element('span',id=alias));ids.add(alias)
  para=target.xpath('.//p[contains(@class,"headline-source")]')[0]
  link=E.SubElement(para,'a',href='../../lean/'+c['source_file']);link.text=' Open source file'
 chapter.insert(0,E.Element('span',id='whole-space-headlines'))
 page=E.Element('html',lang='en');page.append(head);body=E.SubElement(page,'body');nav=E.SubElement(body,'nav',attrib={'aria-label':'Reader navigation'})
 for title,href in [('Home','../'),('Search','../search/'),('Browse the paper','../Browse-the-paper-and-supplement/'),('Third-party notices','../notices/')]:z=E.SubElement(nav,'a',href=href);z.text=title;z.tail=' · '
 main=E.SubElement(body,'main');main.append(chapter);d=out/'Whole-space-fluctuations';d.mkdir(exist_ok=True);(d/'index.html').write_text('<!DOCTYPE html>\n'+E.tostring(page,encoding='unicode',method='html'))
 # Give every baseline page access to the new chapter. Base href makes root paths portable.
 for f in out.rglob('*.html'):
  if f==d/'index.html' or f.parent==out/'notices':continue
  s=H.fromstring(f.read_text());body=s.find('body');base=s.xpath('//base/@href');rel=os.path.relpath(d/'index.html',f.parent)
  href='Whole-space-fluctuations/' if base else rel
  n=E.Element('nav',attrib={'aria-label':'Whole-space chapter'});z=E.SubElement(n,'a',href=href);z.text='Whole-space fluctuations: eight theorems';body.insert(0,n); z=E.SubElement(n,'a',href=('notices/' if base else os.path.relpath(out/'notices/index.html',f.parent)));z.text=' · Third-party notices'
  if f==out/'index.html':
   body.insert(0,E.Element('span',id='hrs-headline-home'))
   if a.with_coverage and (a.tree/'coverage/index.html').exists():
    z=E.SubElement(n,'a',href='../coverage/index.html');z.text=' · Full paper source locator'
  f.write_text('<!DOCTYPE html>\n'+E.tostring(s,encoding='unicode',method='html'))
 # Search index is independent of baseline hover-cache IDs. Preserve baseline hover data.
 for old in (out/'-verso-search').glob('searchIndex*.js'):old.unlink()
 for fresh in (handoff/'search').glob('searchIndex*.js'):shutil.copy2(fresh,out/'-verso-search'/fresh.name)
 if a.with_coverage and (a.tree/'coverage/index.html').exists():
  shutil.copytree(a.tree/'coverage',a.output/'coverage'); mf=a.lean_manifest.read_text()
  frozen=json.loads(mf) if mf.lstrip().startswith('{') else {line.split(maxsplit=1)[1].lstrip('* '):line.split(maxsplit=1)[0] for line in mf.splitlines() if line.strip()}
  for page in (a.output/'coverage').rglob('*.html'):
   doc=H.fromstring(page.read_text());base=doc.xpath('//base/@href');root=(page.parent/(base[0] if base else '.')).resolve()
   for ref in doc.xpath('//*[not(self::base)]/@href|//@src'):
    u=urlsplit(ref)
    if u.scheme or u.netloc:continue
    target=(root/unquote(u.path)).resolve()
    try:rel=target.relative_to((a.output/'lean').resolve())
    except ValueError:continue
    source=a.tree/'lean'/rel
    assert str(rel) in frozen and source.is_file() and sha(source)==frozen[str(rel)],('unverified coverage source',str(rel))
    target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)

# Optional source-bound S11 overlay, before validating enriched coverage links.
s11=a.tree/'blueprint/s11/content.json'
if s11.exists():
 data=json.loads(s11.read_text())
 for card in data['cards']:
  for key in ['file','provider_file']:
   if key not in card:continue
   rel=card[key];source=a.tree/rel;target=a.output/rel
   assert source.is_file() and str(source.resolve()).startswith(str(a.tree.resolve())+os.sep)
   target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
 # Companion sources are a separate, manifest-verified proof supplement, not a base Lean edit.
 supplement=a.tree/'proof-supplement';sm=json.loads((supplement/'INPUTS.json').read_text())
 for module in sm['modules'].values():assert sha(supplement/module['path'])==module['source_sha256'],('companion source changed',module['path'])
 shutil.copytree(supplement,a.output/'proof-supplement',dirs_exist_ok=True)
 subprocess.run(['python3',str(a.tree/'blueprint/s11/render_s11.py'),'--tree',str(a.tree),'--output-root',str(a.output)],env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),check=True,capture_output=True)
 installer=a.tree/'blueprint/s11/install_native_search.py'
 assert installer.is_file(),'S11 native-search installer missing'
 subprocess.run(['python3',str(installer),'--tree',str(a.output)],env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),check=True,capture_output=True)

# Current-source scope note must accompany changed source in either export mode.
for name in ['CURRENT_SOURCE_CHANGES.md']:
 source=a.tree/'lean'/name
 if source.exists():
  target=a.output/'lean'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)

# Reproducible manuscript-first navigation and native search display labels.
from navigation import run as apply_navigation
from search_labels import apply_search_labels
apply_navigation(a.output)
apply_search_labels(out)
from clean_current_search import apply as clean_current_search
clean_current_search(out)

# Offline integrity: every explicit local HTML link/fragment and local resource.
errors=[];checks=0;docs={f.resolve():H.fromstring(f.read_text()) for f in a.output.rglob('*.html')}
idsets={f:set(doc.xpath('//*[@id]/@id')) for f,doc in docs.items()}
for f,doc in docs.items():
 base=doc.xpath('//base/@href');root=(f.parent/(base[0] if base else '.')).resolve()
 for href in doc.xpath('//*[not(self::base)]/@href|//@src'):
  u=urlsplit(href)
  if u.scheme or u.netloc or href.startswith('data:'):continue
  target=(root/unquote(u.path)).resolve() if u.path else f
  if target.is_dir():target/='index.html'
  if not target.exists():errors.append((str(f.relative_to(a.output.resolve())),href,'missing'));continue
  if u.fragment and target in docs and unquote(u.fragment) not in idsets[target]:errors.append((str(f.relative_to(a.output.resolve())),href,'fragment'))
  checks+=1
# Validate all search document destinations as well, not only UI links.
s=(out/'-verso-search/searchIndex.js').read_text();idx=json.JSONDecoder().raw_decode(s.split('=',1)[1].lstrip())[0]
for dest in idx['documentStore']['docs']:
 u=urlsplit(dest);f=(out/u.path.lstrip('/')/'index.html').resolve();frag=unquote(u.fragment)
 if f not in docs or frag not in idsets[f]:errors.append(('search',dest,'destination'))
leaks=[]
for f in out.rglob('*'):
 if f.is_file() and f.suffix in ['.html','.json','.js','.css']:
  s=f.read_text(errors='replace')
  for x in ['/data/','/home/','/workspace/','file://','reader-anchor:']:
   if x in s:leaks.append((str(f.relative_to(out)),x))
report={'scope':'Reassembled frozen editorial baseline plus regenerated whole-space and S11 cards; not a full baseline editorial regeneration or HRS proof build','headline_cards':8,'headline_math_spans':len(new_tex),'s11_cards':len(data['cards']) if s11.exists() else 0,'local_link_checks':checks,'search_destinations':len(idx['documentStore']['docs']),'errors':errors,'leaks':leaks,'output_sha256':{str(f.relative_to(a.output)):sha(f) for f in sorted(a.output.rglob('*')) if f.is_file()}}
(a.output.parent/(a.output.name+'-receipt.json')).write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k!='output_sha256'},indent=2));assert not errors and not leaks,'integrity check failed; see receipt'
