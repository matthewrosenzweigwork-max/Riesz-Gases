#!/usr/bin/env python3
"""Deterministic S11 reader/native-document overlay. Does not alter Lean or run Lean."""
from pathlib import Path as P
import argparse,hashlib,html,json,os,re,subprocess,sys
from lxml import html as H,etree as E
p=argparse.ArgumentParser();p.add_argument('--tree',type=P,required=True);p.add_argument('--content',type=P);p.add_argument('--output-root',type=P);a=p.parse_args();root=a.tree.resolve();dest=(a.output_root or a.tree).resolve();here=P(__file__).resolve().parent
content=a.content or here/'content.json';data=json.loads(content.read_text());presentation=root/'blueprint/presentation';sys.path.insert(0,str(presentation));from mathml_variants import VARIANTS,styled
sha=lambda b:hashlib.sha256(b).hexdigest();esc=lambda s:html.escape(s,quote=True)
source_hashes={};snippets={}
base_manifest={x.split(maxsplit=1)[1].lstrip('* '):x.split(maxsplit=1)[0] for x in (root/'lean/MANIFEST/SHA256SUMS_included_files.txt').read_text().splitlines() if x.strip()}
supp=json.loads((root/'proof-supplement/INPUTS.json').read_text())['modules'];supp_manifest={m['path']:m['source_sha256'] for m in supp.values()}
for c in data['cards']:
 for key,lk,nk in [('file','lines','decl'),('provider_file','provider_lines','provider')]:
  if key not in c:continue
  f=root/c[key];assert f.is_relative_to(root);b=f.read_bytes();source_hashes[c[key]]=sha(b)
  rel=P(c[key]);inventory=base_manifest if rel.parts[0]=='lean' else supp_manifest
  assert sha(b)==inventory[P(*rel.parts[1:]).as_posix()],('frozen source changed',c[key])
  lines=b.decode().splitlines(keepends=True);start,end=c[lk];assert 1<=start<=end<=len(lines)
  text=''.join(lines[start-1:end]);assert c[nk].split('.')[-1] in text,(c[nk],start,end)
  snippets[(c['id'],key)]=text
assert len(data['cards'])==7 and sum('provider' in c for c in data['cards'])==2
pattern=re.compile(r'\$\$(.*?)\$\$|(?<!\$)\$(?!\$)(.*?)\$(?!\$)',re.S)
mds=[data['introduction'],data['setting']]+[c['body'] for c in data['cards']]
tex=[(m[1] is not None,m[1] if m[1] is not None else m[2]) for md in mds for m in pattern.finditer(md)]
node="const k=require('./katex.js'),f=require('fs');process.stdout.write(JSON.stringify(JSON.parse(f.readFileSync(0,'utf8')).map(([displayMode,t])=>k.renderToString(t,{displayMode,output:'mathml',throwOnError:true,strict:'error',trust:false}))));"
renders=json.loads(subprocess.check_output(['node','-e',node],input=json.dumps(tex).encode(),cwd=presentation));cache={}
for key,s in zip(tex,renders):
 x=H.fromstring(s);m=x if x.tag=='math' else x.xpath('.//math')[0];assert m.xpath('.//annotation')[0].text==key[1]
 for el in m.xpath('.//*[@mathvariant]'):
  v=el.get('mathvariant');t=el.text or ''
  if v in VARIANTS and len(t)==1 and not len(el):
   u=styled(t,v)
   if u is not None:el.text=u;el.set('mathvariant','normal')
 m.set('display','block' if key[0] else 'inline');cache[key]=E.tostring(m,encoding='unicode',method='html')
number=0
def prose(md):
 global number
 parts=[];current=''
 def flush():
  nonlocal current
  if current.strip():parts.append('<p>'+current.strip()+'</p>');current=''
 chunks=pattern.split(md)
 for i in range(0,len(chunks),3):
  for j,t in enumerate(re.split(r'\n\s*\n',chunks[i])):
   if j:flush()
   current+=re.sub(r'\*\*(.*?)\*\*',r'<strong>\1</strong>',esc(t)).replace('\n',' ')
  if i+1>=len(chunks):break
  display=chunks[i+1] is not None;t=chunks[i+1] if display else chunks[i+2];math=cache[(display,t)]
  if display:
   flush();number+=1;ident=f's11-eq-{number}';parts.append(f'<div class="equation" id="{ident}"><div class="math-pan" tabindex="0" role="group" aria-label="Mathematical expression; scroll horizontally if needed">{math}</div><a class="eq-number" href="#{ident}" aria-label="Reader equation S11.{number}">(S11.{number})</a></div>')
  else:current+='<span class="inline-math'+(' inline-pan' if len(t)>45 else '')+'"'+(' tabindex="0" role="group" aria-label="Inline expression; scroll horizontally if needed"' if len(t)>45 else '')+'>'+math+'</span>'
 flush();return ''.join(parts)
def source(c,key,label):
 text=snippets[(c['id'],key)];f=c[key];lines=c['lines' if key=='file' else 'provider_lines'];decl=c['decl' if key=='file' else 'provider'];module=P(*P(f).parts[1:]).with_suffix('').as_posix().replace('/','.')
 viewer='../../coverage/source/'+module+'.html#L'+str(lines[0]) if (dest/'coverage/source'/(module+'.html')).exists() else '../../'+f
 return '<details class="lean-code" open><summary>'+esc(label)+'</summary><pre tabindex="0" data-declaration="'+esc(decl)+'" data-source-sha256="'+sha(text.encode())+'">'+esc(text)+'</pre><p class="source-link"><a href="'+viewer+'">'+esc(decl)+'</a> · <a href="../../'+esc(f)+'">source file</a>, lines '+str(lines[0])+'–'+str(lines[1])+'.</p></details>'
css='''html{color-scheme:light;scroll-padding-top:1rem}*{box-sizing:border-box}body{margin:0;background:#fff;color:#191919;font:17px/1.6 system-ui,sans-serif}header,main,.site-nav,footer{width:min(100% - 2rem,1440px);margin:0 auto}.site-nav{padding:1rem 0;display:flex;flex-wrap:wrap;gap:.5rem 1.1rem}header{max-width:90ch;padding:1rem 0}h1,h2,h3{font-family:Georgia,serif;line-height:1.22}h1{font-size:2.2rem}h2{font-size:1.65rem;margin:0 0 1rem}h3{font-size:1.2rem}a{color:#174c8b;text-underline-offset:.15em}a:focus-visible,summary:focus-visible,pre:focus-visible,[tabindex]:focus-visible{outline:3px solid #a64d00;outline-offset:3px}.setting,.evidence-note{max-width:90ch;margin:1.5rem auto}.card{border-top:1px solid #c9cdd1;padding:2rem 0;scroll-margin-top:1rem}.paired{display:grid;grid-template-columns:minmax(0,1.2fr) minmax(0,1fr);gap:2rem}.paired>div{min-width:0}.prose p:first-child{margin-top:0}pre{white-space:pre;overflow:auto;word-break:normal;overflow-wrap:normal;max-width:100%;padding:.8rem;background:#f5f6f8;border:1px solid #c3c9d2;font:14px/1.5 ui-monospace,SFMono-Regular,Consolas,monospace;tab-size:2}summary{cursor:pointer;font-weight:650}.lean-code{margin:0 0 1.25rem}.source-link{font-size:.83rem;overflow-wrap:anywhere}.equation{display:grid;grid-template-columns:minmax(0,1fr) auto;align-items:center;gap:.5rem;margin:1rem 0}.math-pan{max-width:100%;overflow-x:auto;padding:.4em .15em}.eq-number{white-space:nowrap;font-size:.9rem}.inline-pan{display:inline-block;max-width:100%;overflow:auto;vertical-align:middle;padding:.12em .1em}.inline-math>math{max-width:none}.evidence-note{font-size:.94rem;border-left:3px solid #929aa3;padding-left:1rem}.chapter-list{padding-left:1.3rem}.card-label{font-size:.85rem;color:#414951;margin:0 0 .5rem}footer{border-top:1px solid #c9cdd1;padding:1.5rem 0;font-size:.9rem}@media(max-width:1100px){.paired{grid-template-columns:minmax(0,1fr);gap:1rem}header{padding-top:.25rem}h1{font-size:1.85rem}}@media(forced-colors:active){body,pre{background:Canvas;color:CanvasText}a{color:LinkText}.card,.evidence-note,pre{border-color:CanvasText}}@media print{.site-nav{display:none}.paired{display:block}pre{white-space:pre-wrap;overflow-wrap:anywhere}.math-pan{overflow:visible}.card{break-before:auto}.source-link{overflow-wrap:anywhere}}'''
intro=prose(data['introduction']);setting=prose(data['setting']);body=''
for c in data['cards']:
 body+='<section class="card" id="s11-'+esc(c['id'])+'"><p class="card-label">'+('Theorem' if 'provider' in c else 'Definition')+'</p><h2>'+esc(c['title'])+'</h2><div class="paired"><div class="prose">'+prose(c['body'])
 if c['id']=='cubic-tensor':body+='<p><a href="../Whole-space-fluctuations/#headline-eq-S2-10">Three-observation formula: the three terms in Theorem S2.1(iii)</a>.</p>'
 body+='</div><div class="formal">'+source(c,'file','Original Lean declaration (admitted)' if 'provider' in c else 'Lean definition')
 if 'provider' in c:body+=source(c,'provider_file','Companion proof (exact type checked)')
 body+='</div></div></section>'
nav='<nav class="site-nav" aria-label="Reader navigation"><a href="../">Reader home</a><a href="../../coverage/sections/S-S11.html">Supplement §S11 source index</a><a href="../Whole-space-fluctuations/">Whole-space fluctuations</a><a href="../notices/">Third-party notices</a></nav>'
if not (dest/'coverage/sections/S-S11.html').exists():nav=re.sub(r'<a href="../../coverage/sections/S-S11.html">.*?</a>','',nav)
s='<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+esc(data['title'])+' · Fluctuations of Riesz gases</title><style>'+css+'</style></head><body><a href="#main" class="site-nav">Skip to content</a>'+nav+'<header><p>Supplement §S11</p><h1>'+esc(data['title'])+'</h1>'+intro+'<ol class="chapter-list">'+''.join('<li><a href="#s11-'+esc(c['id'])+'">'+esc(c['title'])+'</a></li>' for c in data['cards'])+'</ol></header><main id="main"><section class="setting" aria-labelledby="s11-setting"><h2 id="s11-setting">Setting and notation</h2>'+setting+'</section><aside class="evidence-note"><p>The original Lean declarations for Proposition S11.1 and Corollary S11.2 contain <code>sorry</code>. Their separate companion proofs have the same types and use only standard axioms. Both are shown below; see the <a href="../../proof-supplement/README.md">proof supplement</a> and <a href="../../coverage/sections/S-S11.html">source index</a>.</p><p>Equation labels (S11.1), (S11.2), … number displays in this reader. They are not additional manuscript result numbers.</p></aside>'+body+'</main><footer>Lean supplies the mathematical statements. Manuscript sections and result numbers supply navigation.</footer></body></html>'
if not (dest/'coverage/sections/S-S11.html').exists():s=s.replace(' and <a href="../../coverage/sections/S-S11.html">source index</a>','')
page=dest/'reader/Relaxation-on-moving-windows/index.html';page.parent.mkdir(exist_ok=True);page.write_text(s)
d=H.fromstring(s);assert [x.text_content() for x in d.xpath('//annotation')]==[t for _,t in tex];assert len(d.xpath('//pre'))==9
for el in d.xpath('//pre'):assert sha(el.text_content().encode())==el.get('data-source-sha256')
assert len(set(d.xpath('//*[@id]/@id')))==len(d.xpath('//*[@id]/@id'))
# Minimal idempotent navigation overlays, preserving all existing page content.
def inject(file,ident,fragment,where='body'):
 s=file.read_text();start='<!-- '+ident+':start -->';end='<!-- '+ident+':end -->';s=re.sub(re.escape(start)+'.*?'+re.escape(end),'',s,flags=re.S);chunk=start+fragment+end
 if where=='body':s=re.sub(r'(<body[^>]*>)',lambda m:m[0]+chunk,s,count=1)
 elif where=='main':s=re.sub(r'(<main[^>]*>)',lambda m:m[0]+chunk,s,count=1)
 else:s=s.replace('</body>',chunk+'</body>',1)
 file.write_text(s)
links='<nav aria-label="Relaxation on moving windows"><a href="Relaxation-on-moving-windows/#s11-tensor-relaxation">Proposition S11.1: tensor relaxation</a> · <a href="Relaxation-on-moving-windows/#s11-two-parameter-edgeworth">Corollary S11.2: stationary correction</a></nav>'
inject(dest/'reader/index.html','hrs-s11-reader-nav',links)
inject(dest/'reader/Browse-the-paper-and-supplement/index.html','hrs-s11-reader-nav',links)
clinks='<nav aria-label="Read section S11"><a href="../../reader/Relaxation-on-moving-windows/#s11-tensor-relaxation">Read Proposition S11.1</a> · <a href="../../reader/Relaxation-on-moving-windows/#s11-two-parameter-edgeworth">Read Corollary S11.2</a></nav>'
if (dest/'coverage/sections/S-S11.html').exists():inject(dest/'coverage/sections/S-S11.html','hrs-s11-reader-nav',clinks,'main')
if (dest/'coverage/index.html').exists():inject(dest/'coverage/index.html','hrs-s11-reader-nav','<nav aria-label="Section S11 reader"><a href="../reader/Relaxation-on-moving-windows/">§S11: Relaxation on moving windows</a></nav>','main')
# A direct link to the cubic formula must open its enclosing notation disclosure.
script='<script id="hrs-s11-target-disclosure">(()=>{function reveal(){let e=document.getElementById(decodeURIComponent(location.hash.slice(1)));if(!e)return;for(let p=e.parentElement;p;p=p.parentElement)if(p.tagName==="DETAILS")p.open=true;requestAnimationFrame(()=>e.scrollIntoView({block:"start"}));}addEventListener("hashchange",reveal);if(location.hash)reveal();})();</script>'
inject(dest/'reader/Whole-space-fluctuations/index.html','hrs-s11-target-disclosure',script,'end')
f=dest/'README.md';t=f.read_text() if f.exists() else '';line='- [Relaxation on moving windows (§S11)](reader/Relaxation-on-moving-windows/index.html): covariance and cubic-tensor relaxation, the stationary first correction, and five definitions, with exact Lean declarations and the two companion proofs.\n';t=re.sub(r'^- \[Relaxation on moving windows.*\n','',t,flags=re.M);t=t.replace('- [Frozen Lean package]',line+'- [Frozen Lean package]',1);
if f.exists():f.write_text(t)
# Native document sources are generated from the same prose, not treated as compiled here.
def vm(md):return pattern.sub(lambda m:('$$`'+m[1].strip()+'`') if m[1] is not None else ('$`'+m[2]+'`'),md)
if not a.output_root:
 native='import HRS.Whole.Window\nimport Verso\nimport VersoManual\nimport VersoBlueprint\nopen Verso.Genre Verso.Genre.Manual Informal\n\n#doc (Manual) "'+data['title']+'" =>\n\n%%%\ntag := "s11-moving-windows"\n%%%\n\n'+vm(data['introduction'])+'\n\n# Setting and notation\n\n'+vm(data['setting'])+'\n\nThe frozen theorem declarations contain admissions. Separate companion proofs have matching types; see the proof supplement.\n\n'
 for c in data['cards']:
  native+='# '+c['title']+'\n\n%%%\ntag := "s11-'+c['id']+'"\n%%%\n\n:::'+('theorem' if 'provider' in c else 'definition')+' "s11-'+c['id']+'-declaration" (lean := "'+c['decl']+'")\n'+vm(c['body'])+'\n:::\n\n'
  if 'provider' in c:native+='Companion proof (exact type checked): `'+c['provider']+'`.\n\n```\n'+snippets[(c['id'],'provider_file')]+'```\n\n'
 (here/'S11.lean').write_text(native)
 contents=(root/'blueprint/candidate-headlines/HeadlineContents.lean').read_text().replace('import Headline\n','import Headline\nimport S11\n',1).replace('tag := "hrs-headline-home"','tag := "hrs-s11-home"').replace('{include 0 Headline}','{include 0 Headline}\n\n{include 0 S11}')
 (here/'S11Contents.lean').write_text(contents);(here/'MainS11.lean').write_text((root/'blueprint/candidate-headlines/MainHeadline.lean').read_text().replace('HeadlineContents','S11Contents'))
 (here/'content.json').write_bytes(content.read_bytes())
receipt={'scope':'Source-bound static reader and native document sources; native compilation requires separate receipt','cards':len(data['cards']),'theorems':2,'definitions':5,'tex_spans':len(tex),'display_equations':number,'source_blocks':9,'source_hashes':source_hashes,'content_sha256':sha(content.read_bytes()),'page_sha256':sha(page.read_bytes()),'native_sources':{n:sha((here/n).read_bytes()) for n in ['S11.lean','S11Contents.lean','MainS11.lean']}}
((dest.parent/(dest.name+'-s11-receipt.json')) if a.output_root else here/'render-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
