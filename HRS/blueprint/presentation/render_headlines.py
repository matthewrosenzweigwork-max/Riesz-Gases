from pathlib import Path as P
import json,re,html,hashlib,subprocess,sys,os
from collections import defaultdict
from lxml import html as H,etree as E
sys.path[:0]=[str(P(os.environ.get('HRS_MATH_STYLE','rc4-work')).resolve())]
from mathml_variants import VARIANTS,styled
w=P(os.environ.get('HRS_HEADLINE_WORK','hrs-release-map/headlines'));a=json.loads((w/'equilibrium-and-paths.json').read_text());b=json.loads((w/'preparation-and-fields.json').read_text());allcards=a[:3]+b[:2]+b[2:]+a[3:]
groups={c['name'].split('.')[-1]:g for c,g in zip(allcards,['S2']*3+['S3']*2+['S5']*3)}
titles=['Theorem S2.1(i)','Theorem S2.1(ii)','Theorem S2.1(iii)','Corollary S3.2 · preparation bounds','Corollary S3.2 · stationary transfer','Proposition S5.3 · field remainder','Proposition S5.3 · centered field remainder','Theorem S5.6']
ids=['headline-'+c['name'].split('.')[-1].replace('_','-') for c in allcards];shorts=[c['name'].split('.')[-1] for c in allcards]
base=P(os.environ.get('HRS_READER_BASE','hrs-disclosure/delivery/HRS-compact-reading-copy.html')).read_text();esc=lambda t:html.escape(t,quote=False)
texpat=re.compile(r'\$\$(.*?)\$\$|(?<!\$)\$(?!\$)(.*?)\$(?!\$)',re.S)
gloss=(w/'conventions.md').read_text().strip()
tex=[]
for c in [{'english':gloss}]+allcards:
 tex+=list((m[1] is not None,m[1] if m[1] is not None else m[2]) for m in texpat.finditer(c['english']))
assert not any(not t.strip() for d,t in tex)
node="""const k=require('./katex.js'),fs=require('fs');process.stdout.write(JSON.stringify(JSON.parse(fs.readFileSync(0,'utf8')).map(([displayMode,t])=>k.renderToString(t,{displayMode,output:'mathml',throwOnError:true,strict:'error'}))))"""
cache=json.loads(subprocess.check_output(['node','-e',node],input=json.dumps(tex).encode(),cwd=w.resolve()))
assert len(cache)==len(tex)
cat={}
for k,v in zip(tex,cache):
 x=H.fromstring(v);m=x if x.tag=='math' else x.xpath('.//math')[0];ann=m.xpath('.//annotation')[0];assert ann.text==k[1]
 for e in m.xpath('.//*[@mathvariant]'):
  variant=e.get('mathvariant');t=e.text or ''
  if variant in VARIANTS and len(t)==1 and not len(e):
   u=styled(t,variant)
   if u is not None:e.text=u;e.set('mathvariant','normal')
 m.set('display','block' if k[0] else 'inline');cat[k]=E.tostring(m,encoding='unicode',method='html')
num=defaultdict(int);count=0
def para(md,g):
 global count
 chunks=texpat.split(md);res=[]; current=''
 def flush():
  nonlocal current
  if current.strip():res.append('<p>'+current.strip()+'</p>');current=''
 def text(t):
  nonlocal current
  for j,u in enumerate(re.split(r'\n\s*\n',t)):
   if j:flush()
   current+=re.sub(r'\*\*(.*?)\*\*',r'<strong>\1</strong>',esc(u)).replace('\n',' ')
 for j in range(0,len(chunks),3):
  text(chunks[j]); 
  if j+1>=len(chunks):break
  disp=chunks[j+1] is not None; val=chunks[j+1] if disp else chunks[j+2];m=cat[(disp,val)];count+=1
  if disp:
   flush();num[g]+=1;label=f'{g}.{num[g]}';ident='headline-eq-'+label.replace('.','-');res.append(f'<div class="hrs-card-equation" id="{ident}"><div class="hrs-card-math display math-pan" tabindex="0" role="group" aria-label="Mathematical expression; scroll horizontally if needed">{m}</div><a class="hrs-card-number" href="#{ident}" aria-label="Reader equation {label}">({label})</a></div>')
  else:
   if len(val)>32:current+='<span class="hrs-headline-inline-pan" tabindex="0" role="group" aria-label="Inline mathematical expression; scroll horizontally if needed">'+m+'</span>'
   else:current+='<span>'+m+'</span>'
 flush();return ''.join(res)
def split(md,short):
 if '\n### ' in md:
  h,n=md.split('\n### ',1);t,n=n.split('\n',1);return h,t.strip(),n
 markers={'whole_space_stationary':'Here $d_2$','whole_space_prepared':'In the decay hypothesis','whole_space_edgeworth':'The tensor is specified','general_paths':'Fix a smooth compactly'}
 marker=markers.get(short);at=md.index(marker);return md[:at],'Tensor on three observations' if short=='whole_space_edgeworth' else 'Notation and hypotheses',md[at:]
def codebox(name,kind,s):
 cls='hrs-author-source' if kind=='statement' else 'hrs-source-proof';return '<details class="hrs-headline-code"'+(' open' if kind=='statement' else '')+'><summary>Exact Lean '+kind+'</summary><pre tabindex="0" class="'+cls+'" data-source-declaration="'+name+'" data-source-sha256="'+hashlib.sha256(s.encode()).hexdigest()+'">'+esc(s)+'</pre></details>'
def btitle(i):return titles[i]+' · '+allcards[i]['title']
head='<article id="hrs-whole-space-headlines" class="native-reading-page hrs-headline-chapter"><header><h1>Whole-space fluctuations</h1><p>For quadratic confinement, the particle field has a Gaussian approximation at equilibrium and under small perturbations, with a cubic correction in the Hilbert–Schmidt range. The preparation and remainder estimates below also enter the comparison of paths at varying temperature.</p></header><nav aria-label="Whole-space statements"><ol>'+''.join(f'<li><a href="#{id}">{esc(btitle(i))}</a></li>' for i,id in enumerate(ids))+'</ol></nav><p class="headline-scope">Equation numbers on this page refer to the reader. Paper references are given in the headings. The eight Lean declarations use only the standard axioms in the checked environment.</p>'
gloss_html=para(gloss,"S2")
parts=[];verso=[]
for i,c in enumerate(allcards):
 name=c['name'];short=shorts[i];g=groups[short];main,label,more=split(c['english'],short)
 core=para(main,g);note=para(more,g)
 if i<3 or i==7:note='<p><a href="#headline-conventions">Function spaces and mean-field equation</a></p>'+note
 f=c['source_file'];line=c['source_line'];sig=c['exact_signature'];proof=c['exact_proof']
 # Source is shown alongside English; no one-line fragment wrapping introduced.
 s='<section id="'+ids[i]+'"><h2>'+esc(btitle(i))+'</h2>'+core+'<details class="hrs-notation"><summary>'+esc(label)+'</summary>'+note+'</details>'+codebox(name,'statement',sig)+codebox(name,'proof',proof)+'<p class="headline-source"><code>'+esc(name)+'</code> · <code>'+esc(f)+'</code>, line '+str(line)+'.</p></section>'
 parts.append(s)
 def vm(md):
  # Protect each multiline math span before converting paragraphs.
  return texpat.sub(lambda x: ('$$'+chr(96)+x[1].strip()+chr(96)) if x[1] is not None else ('$'+chr(96)+x[2]+chr(96)),md).replace('**','*')
 verso.append('# '+btitle(i)+'\n\n%%%\ntag := "'+ids[i]+'"\n%%%\n\n:::theorem "'+ids[i]+'-provider" (lean := "'+name+'")\n'+vm(main).strip()+'\n:::\n\n## '+label+'\n\n'+vm(more).strip()+'\n\nExact Lean source: '+chr(96)+name+chr(96)+'.\n\n'+chr(96)*3+'\n'+sig+' :=\n'+proof+'\n'+chr(96)*3)
head+='<details id="headline-conventions" class="hrs-notation"><summary>Function spaces and mean-field equation</summary>'+gloss_html+'</details>'
chapter=head+''.join(parts)+'</article>'
newcss='<style id="hrs-headline-style">.hrs-headline-chapter .hrs-card-equation{display:grid;grid-template-columns:minmax(0,1fr) auto;align-items:center;gap:.5rem;margin:.7rem 0}.hrs-headline-chapter .math-pan{max-width:100%;overflow-x:auto;padding:.3em .15em}.hrs-headline-chapter .hrs-card-number{white-space:nowrap}.hrs-headline-inline-pan{display:inline-block;max-width:100%;overflow-x:auto;overflow-y:hidden;vertical-align:middle;padding:.24em .13em .28em}.hrs-headline-inline-pan>math{max-width:none}.hrs-headline-chapter .hrs-author-source,.hrs-headline-chapter .hrs-source-proof{white-space:pre;max-width:100%;overflow:auto;overflow-wrap:normal;word-break:normal}.hrs-headline-chapter section{min-width:0}.hrs-headline-chapter summary{font-weight:600}.hrs-headline-chapter .headline-scope,.hrs-headline-chapter .headline-source{font-size:.91em}.hrs-headline-chapter h2{margin-top:2em}</style>'
link='<a href="#hrs-whole-space-headlines">Whole-space fluctuations</a>'
s=base.replace('</head>',newcss+'</head>',1).replace('>Evidence</a></nav>','>Evidence</a>'+link+'</nav>',1).replace('</main>',chapter+'</main>',1)
assert s.count(link)==1 and s.count('id="hrs-whole-space-headlines"')==1
p=w/'HRS-whole-space-reading-copy.html';p.write_text(s);old=H.fromstring(base);new=H.fromstring(s);select=lambda t,cls:t.xpath('//*[contains(concat(" ",normalize-space(@class)," ")," '+cls+' ")]')
assert len(new.xpath('//math//annotation'))-len(old.xpath('//math//annotation'))==count==len(tex)
assert [x.text_content() for x in select(new,'hrs-author-source')]==[x.text_content() for x in select(old,'hrs-author-source')]+[c['exact_signature'] for c in allcards]
assert [x.text_content() for x in select(new,'hrs-source-proof')]==[x.text_content() for x in select(old,'hrs-source-proof')]+[c['exact_proof'] for c in allcards]
assert not new.xpath('//details[contains(@class,"hrs-notation")]//details[contains(@class,"hrs-notation")]')
assert all(x[1:] in set(new.xpath('//*[@id]/@id')) for x in new.xpath('//a[starts-with(@href,"#")]/@href'))
assert not new.xpath('//script|//iframe')
(w/'chapter.html').write_text(chapter)
v='import HRS.Whole.Headline\nimport Verso\nimport VersoManual\nimport VersoBlueprint\nopen Verso.Genre Verso.Genre.Manual Informal\n\n#doc (Manual) "Whole-space fluctuations" =>\n\n%%%\ntag := "whole-space-headlines"\n%%%\n\n'+vm(gloss)+'\n\n'+ '\n\n'.join(verso)+'\n'
(w/'Headline.lean').write_text(v)
(w/'receipt.json').write_text(json.dumps(dict(new_formulas=count,equations=dict(num),theorems=8,source_blocks=len(select(new,'hrs-author-source')),proofs=len(select(new,'hrs-source-proof')),size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2));print((w/'receipt.json').read_text())
