#!/usr/bin/env python3
"""Remove withdrawn D.6 content from served search, retaining historical input snapshots."""
from pathlib import Path
import json,re,subprocess,tempfile
REMOVED='/Browse-the-paper-and-supplement/#sample-6'
SCOPE='/The-sharp-sub-Coulomb-commutator/#Fluctuations-of-Riesz-gases--The-sharp-sub-Coulomb-commutator--Lean-declarations-and-evidence--Scope-of-the-exposition'
SENTENCE=' The distinct truncated-kernel statement in Appendix D.6 is listed with its admitted proof in the index.'
def apply(reader):
 reader=Path(reader);root=reader/'-verso-search';p=root/'searchIndex.js';s=p.read_text();start=s.index('=')+1
 match=re.search(r'\S',s[start:]);start+=match.start();data,end=json.JSONDecoder().raw_decode(s[start:]);end+=start
 olddocs={};newscope=None
 for shard in sorted(root.glob('searchIndex_*.js')):
  raw=shard.read_text();m=re.fullmatch(r'(window\.docContents\[\d+\]\.resolve\()(.*)(\);\s*)',raw,re.S)
  if not m:continue
  docs=json.loads(m[2]);changed=False
  if REMOVED in docs:
   olddocs[REMOVED]=docs.pop(REMOVED);changed=True
  if SCOPE in docs and SENTENCE in docs[SCOPE]['contents']:
   olddocs[SCOPE]=json.loads(json.dumps(docs[SCOPE]));docs[SCOPE]['contents']=docs[SCOPE]['contents'].replace(SENTENCE,'');newscope=docs[SCOPE];changed=True
  if changed:shard.write_text(m[1]+json.dumps(docs,ensure_ascii=False,separators=(',',':'))+m[3])
 # Original documents are not stored in the compact index. Remove all of their
 # postings explicitly; rebuild only the surviving short prose entry with the
 # shipped elasticlunr pipeline. All unrelated posting values remain identical.
 if REMOVED in data['documentStore']['docs']:
  assert REMOVED in olddocs and SCOPE in olddocs and newscope
  before=json.loads(json.dumps(data))
  def strip(node):
   if isinstance(node,dict):
    if isinstance(node.get('docs'),dict):
     for ident in [REMOVED,SCOPE]:node['docs'].pop(ident,None)
     node['df']=len(node['docs'])
    for k,v in list(node.items()):
     if k!='docs':strip(v)
  for index in data['index'].values():strip(index['root'])
  for key in ['docs','docInfo']:
   for ident in [REMOVED,SCOPE]:data['documentStore'][key].pop(ident,None)
  data['documentStore']['length']=len(data['documentStore']['docs'])
  code="""const fs=require('fs'),elasticlunr=require(process.argv[1]);const x=JSON.parse(fs.readFileSync(0,'utf8'));const idx=elasticlunr.Index.load(x.index);idx.addDoc(x.doc,false);process.stdout.write(JSON.stringify(idx.toJSON()));"""
  out=subprocess.run(['node','-e',code,str((root/'elasticlunr.min.js').resolve())],input=json.dumps({'index':data,'doc':newscope}),text=True,capture_output=True,check=True)
  data=json.loads(out.stdout)
  # Keep compact-document representation used by the native index.
  data['documentStore']['docs'][SCOPE]={}
  assert data['documentStore']['length']==int(before['documentStore']['length'])-1
  assert set(data['documentStore']['docs'])==set(before['documentStore']['docs'])-{REMOVED}
  for ident,info in before['documentStore']['docInfo'].items():
   if ident not in [REMOVED,SCOPE]:assert data['documentStore']['docInfo'][ident]==info
  def postings(node,path='',out=None):
   if out is None:out={}
   if isinstance(node,dict):
    if 'docs' in node:out[path]={k:v for k,v in node['docs'].items()if k not in [REMOVED,SCOPE]}
    for k,v in node.items():
     if k not in ['docs','df']:postings(v,path+'/'+k,out)
   return {k:v for k,v in out.items()if v}
  for field in before['index']:assert postings(before['index'][field])==postings(data['index'][field]),field
  p.write_text(s[:start]+json.dumps(data,ensure_ascii=False,separators=(',',':'))+s[end:])
 else:assert not olddocs,'inconsistent cleaned index and shards'
 # Keep an inert resolver alias for pre-existing find/?name=sample-6 links.
 # It no longer carries the obsolete result label; the UI excludes this alias.
 p=reader/'xref.json';xref=json.loads(p.read_text());records=xref['Verso.Genre.Manual.section']['contents'].get('sample-6',[])
 for entry in records:
  d=entry['data'];d['title']='Appendix D · Smooth scale truncation';d['sectionNum']=None;d['shortTitle']=None
  d['context']=[x for x in d.get('context',[]) if x.get('title')!='Truncated commutator']
 p.write_text(json.dumps(xref,ensure_ascii=False,separators=(',',':'))+'\n')
 for shard in root.glob('searchIndex*.js'):
  raw=shard.read_text();assert 'fdl_commutator' not in raw and 'lemma D.6' not in raw and 'Appendix D.6' not in raw,shard
 assert REMOVED not in p.with_name('-verso-search').joinpath('searchIndex.js').read_text()
if __name__=='__main__':
 import sys
 apply(Path(sys.argv[1]))
