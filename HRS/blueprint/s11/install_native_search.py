"""Install the actual compiled and source-checked S11 native search payload into an already rendered reader."""
from pathlib import Path as P
import argparse,hashlib,json,re,shutil
from lxml import html as H
from urllib.parse import urlsplit,unquote
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--tree',type=P,required=True,help='The assembled HRS tree, containing reader/');a=p.parse_args()
src=P(__file__).resolve().parent; tree=a.tree.resolve();reader=tree/'reader'; hand=src/'native-search';sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
mf=json.loads((hand/'manifest.json').read_text());assert mf['schema']=='hrs-s11-native-search-v1' and mf['raw_document_receipt_sha256']=='63bc199ae108da8a7b54ee1235781a6afb1a312b74a4591f9a00b0e38815bd7d' and len(mf['compiled_document_modules'])==12 and mf['all_document_commands_exit_zero']
s11=reader/'Relaxation-on-moving-windows/index.html'; home=reader/'index.html'
def alias(p,old,new,marker):
 s=p.read_text()
 if marker in s:assert new in s;return
 assert s.count(old)==1,(p.name,old);p.write_text(s.replace(old,new,1))
alias(s11,'<h1>Relaxation on moving windows','<h1 id="s11-moving-windows">Relaxation on moving windows','id="s11-moving-windows"')
long='Fluctuations-of-Riesz-gases--Relaxation-on-moving-windows--Setting-and-notation'
alias(s11,'class="setting" aria-labelledby="s11-setting"','id="'+long+'" class="setting" aria-labelledby="s11-setting"','id="'+long+'"')
alias(home,'<nav aria-label="Relaxation on moving windows"','<nav id="hrs-s11-home" aria-label="Relaxation on moving windows"','id="hrs-s11-home"')
page=H.fromstring(s11.read_bytes());canon=lambda s:re.sub(r'\s+','',s);tex=[canon(x.text_content()) for x in page.xpath('//annotation')]
assert tex==[canon(x)for x in mf['ordered_tex']] and len(tex)==97,'raw and finished mathematics differ'
c=json.loads((src/'content.json').read_text());named={x['id']:x['decl']for x in c['cards']};assert named==mf['source_bindings']
for card,decl in named.items():assert decl in page.get_element_by_id('s11-'+card).text_content()
alljs=mf['search_assets'];assert len(alljs)==84 and set(alljs)=={p.name for p in hand.glob('searchIndex*.js')}
dest=reader/'-verso-search'
for n,h in alljs.items():
 assert re.fullmatch(r'searchIndex(?:_[0-9]+\.[a-f0-9]+)?\.js',n) and sha(hand/n)==h,n
 if not (dest/n).exists() or sha(dest/n)!=h:shutil.copyfile(hand/n,dest/n)
# Keep old fingerprinted shards in the full release: already open reader tabs can resolve the old index too.
idx=json.JSONDecoder().raw_decode((dest/'searchIndex.js').read_text().split('=',1)[1].lstrip())[0];cache={}
for u in idx['documentStore']['docs']:
 v=urlsplit(u);q=reader/v.path.lstrip('/')/'index.html';assert q.is_file(),u
 if q not in cache:cache[q]=set(H.fromstring(q.read_bytes()).xpath('//*[@id]/@id'))
 assert not v.fragment or unquote(v.fragment) in cache[q],u
assert len(idx['documentStore']['docs'])==mf['search_destinations']==104 and len(mf['new_s11_destinations'])==9
print('Installed compiled native search: 104 verified destinations, including nine S11 destinations; seven declaration bindings and 97 ordered TeX expressions checked.')
