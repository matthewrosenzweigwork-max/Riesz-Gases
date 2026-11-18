#!/usr/bin/env python3
"""Extract a sanitized whitelist from genuine compiled native output; never executes it."""
from pathlib import Path as P
import argparse,json,hashlib,re,shutil
from lxml import html as H
p=argparse.ArgumentParser();p.add_argument('--raw',type=P,required=True);p.add_argument('--tree',type=P,required=True);p.add_argument('--output',type=P,required=True);p.add_argument('--verify-against',type=P);p.add_argument('--verified-raw-lock',type=P);a=p.parse_args()
here=P(__file__).resolve().parent;lock=json.loads((here/'INPUTS.json').read_text());sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
for rel,h in lock['tree_inputs'].items():assert sha(a.tree/rel)==h,('native/source input changed',rel)
if not a.verify_against:
 assert a.verified_raw_lock,'initial extraction requires independently verified raw hash inventory'
 for rel,h in json.loads(a.verified_raw_lock.read_text()).items():assert sha(a.raw/rel)==h,('verified raw input changed',rel)
A=json.loads((here/'writer-a.json').read_text());B=json.loads((here/'writer-b.json').read_text());cards=A[:3]+B+A[3:]
raw=H.fromstring((a.raw/'Whole-space-fluctuations/index.html').read_text());tex=lambda s:re.sub(r'\s+','',s)
math=lambda e:[tex(x.text_content()) for x in e.xpath('.//*[contains(concat(" ",normalize-space(@class)," ")," bp_math ")]')]
native_source=(a.tree/'blueprint/candidate-headlines/Headline.lean').read_text()
entries=[]
for c in cards:
 ident='headline-'+c['name'].split('.')[-1].replace('_','-');s=raw.get_element_by_id(ident).getparent();assert s.tag=='section'
 assert ('(lean := "'+c['name']+'")') in native_source
 decls=s.xpath('.//li[contains(@id,"--informal-external-decl-")]');matches=[e for e in decls if e.get('id','').endswith(c['name'].replace('.','___'))]
 assert len(matches)==1 and c['name'] in s.text_content(),c['name']
 entries.append({'id':ident,'declaration':c['name'],'ordered_tex':math(s),'aliases':s.xpath('.//*[@id]/@id')})
manifest={'format':'hrs-native-handoff-v1','native_sources':{k:v for k,v in lock['tree_inputs'].items() if k.endswith('.lean') and k.startswith('blueprint/')},'ordered_tex':math(raw),'cards':entries,'search_assets':{f.name:sha(f) for f in sorted((a.raw/'-verso-search').glob('searchIndex*.js'))}}
# Preserve only canonical mathematical bindings, alias anchors and generated search shards.
payload=json.dumps(manifest,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
for forbidden in ['/data/','/home/','/workspace/','file://','reader-anchor:']:
 assert forbidden not in payload,('unsafe canonical value',forbidden)
 for f in (a.raw/'-verso-search').glob('searchIndex*.js'):assert forbidden not in f.read_text(),('unsafe search shard',f.name,forbidden)
if a.verify_against:assert json.loads((a.verify_against/'manifest.json').read_text())==manifest,'semantic native handoff diverged'
assert not a.output.exists();a.output.mkdir(parents=True);(a.output/'manifest.json').write_text(payload);(a.output/'search').mkdir()
for f in (a.raw/'-verso-search').glob('searchIndex*.js'):shutil.copy2(f,a.output/'search'/f.name)
print('canonical handoff',len(entries),'cards',len(manifest['ordered_tex']),'math',len(manifest['search_assets']),'search assets')
