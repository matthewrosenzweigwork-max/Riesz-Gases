"""Build the static paper locator. Inputs are frozen, reviewed files; no network or JavaScript required."""
from pathlib import Path as P
import argparse,csv,html,json,hashlib,collections,re,os,shutil
from urllib.parse import quote
ap=argparse.ArgumentParser()
for a in ['tree','inventory','titles','providers','output']:ap.add_argument('--'+a,type=P,required=True)
a=ap.parse_args();H=a.tree.resolve();I=a.inventory.resolve();O=a.output.resolve();O.mkdir(parents=True,exist_ok=False)
C=H/'coverage';(O/'source').mkdir();(O/'sections').mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def tsv(p):return list(csv.DictReader(p.open(),delimiter='\t'))
def esc(x):return html.escape(str(x),quote=True)
def anc(s):return 'p-'+hashlib.sha256(s.encode()).hexdigest()[:14]
def modid(s):return s[:-5].replace('/','.')
def section_title(k):
 doc,n=k.split('-',1);return (('Main appendix '+n) if doc=='M' and n.isalpha() else ('Supplement appendix '+n.split('.')[-1]) if n.startswith('S.') else ('Main §' if doc=='M' else 'Supplement §')+n)
def url(p):return quote(p,safe='/.#-_')
heads=tsv(C/'headings.tsv');hg={x['id']:x for x in heads};targets=tsv(C/'paper-sources.tsv');target={x['source_id']:x for x in targets};claims=tsv(C/'claim-locators.tsv');loc=tsv(I/'declaration-locators.tsv');axi={x['name']:x for x in tsv(I/'current-axioms.tsv')};titles=json.loads(a.titles.read_text());providers=json.loads(a.providers.read_text()); inputs=json.loads((I/'inputs.json').read_text())
for f in ('declaration-locators.tsv','current-axioms.tsv'):shutil.copyfile(I/f,O/f)
assert len(loc)==len(claims)==1182 and len(axi)==1151
extra=json.loads((I/'supplemental.json').read_text()); positions={x['qualified_name']:x for x in loc if x['qualified_name']};positions.update(extra)
by=collections.defaultdict(list)
for x,y in zip(claims,loc):
 assert x['ledger_line']==y['ledger_line'] and x['claim_token']==y['token'] and x['paper_source_id']==y['source_id'];by[x['paper_source_id']].append((x,y))
for v in providers.values():
 for p in v.get('sources',[]): 
  if p.get('name'):positions.setdefault(p['name'],p)
paperrows=collections.defaultdict(list)
for r in targets:
 k=r['heading_ids'].split(';');start=int(r['first_line']);ss=[i for i in k if hg[i]['kind']=='section' and int(hg[i]['start'])<=start<=int(hg[i]['end'])];sub=[i for i in k if hg[i]['kind']=='subsection' and int(hg[i]['start'])<=start<=int(hg[i]['end'])]
 assert len(ss)==1 and len(sub)<=1;r['home']=ss[0];r['sub']=sub[0] if sub else '';paperrows[(r['home'],r['sub'])].append(r)
 for i in k:
  if hg[i]['kind']=='section' and i!=r['home']:paperrows[(i,'cross')].append(r)
def source_url(p,pre):return pre+'source/'+url(modid(p['file']))+'.html#L'+str(p['line'])
checks=O/'checks';checks.mkdir();shutil.copyfile(a.providers.parent/'ProofBindings.lean',checks/'ProofBindings.lean')
if any(v.get('from_supplement') for v in providers.values()):
 shutil.copyfile(H/'proof-supplement/ExactTypes.lean',checks/'WholeSpaceSupplement.lean')
def htm(title,main,depth=0):
 pre='../'*depth
 return '<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="color-scheme" content="light"><title>'+esc(title)+' · Fluctuations of Riesz gases</title><link rel="icon" type="image/svg+xml" href="'+pre+'mark.svg"><link rel="stylesheet" href="'+pre+'coverage.css"></head><body><a class="skip" href="#main">Skip to content</a><header><nav aria-label="Project"><a href="'+pre+'../reader/index.html">Mathematical reader</a><a href="'+pre+'index.html">Paper index</a><a href="'+pre+'evidence.html">Reading the evidence</a></nav></header><main id="main">'+main+'</main></body></html>\n'
css=""":root{color-scheme:only light;background:white;color:#1d2023;font-family:system-ui,sans-serif}*{box-sizing:border-box}body{margin:0;background:#fff;color:#1d2023}header{border-bottom:1px solid #a5a9aa}header>nav,main{max-width:76rem;margin:auto;padding:1rem clamp(1rem,3vw,2.6rem)}header>nav{display:flex;gap:1.3rem;flex-wrap:wrap}main{padding-block:1.65rem 4rem}a{color:#194b67;text-underline-offset:.13em}a:visited{color:#413c63}h1,h2,h3,h4{font-family:Georgia,serif;line-height:1.2;overflow-wrap:anywhere}h1{font-size:clamp(1.8rem,4vw,3.15rem);margin-block:.4rem 1rem}h2{font-size:clamp(1.45rem,3vw,2.05rem);margin-top:2rem}h3{font-size:1.25rem}p,li{line-height:1.55}p{max-width:79ch}code,.name{font-family:ui-monospace,monospace;overflow-wrap:anywhere;font-size:.92em}.kicker,.muted{color:#4d5257;font-size:.88rem}.target{border-block-start:1px solid #d6d8da;padding:.4rem 0 1.1rem}.list{padding-left:1.3rem}.records{padding-left:1.25rem}.records li{margin:.75rem 0}.records small{display:block;line-height:1.5}.record-status{font-weight:600}.warn{color:#713512}.guide{background:#f5f6f7;padding:.65rem 1.25rem;border-inline-start:.24rem solid #3f5568}.tag{font-size:.87rem}.jump{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,21rem),1fr));gap:.3rem 2rem}.jump li{margin-block:.3rem}.source{max-width:100%;overflow-x:auto;border:1px solid #c4c8ca;border-radius:.2rem;background:white;color:#181a1d;padding:.5rem 0;line-height:1.5;tab-size:2}.source>code{font-size:.88rem;overflow-wrap:normal;white-space:pre}.source .line{display:block;min-width:max-content;padding-right:1rem}.source .ln{display:inline-block;min-width:4.2em;margin-right:1rem;text-align:right;color:#585b5d;user-select:none}.line:target{background:#fff1c5}.skip:not(:focus){position:absolute;clip-path:inset(100%)}:focus-visible{outline:3px solid #17628e;outline-offset:3px}summary{cursor:pointer;width:fit-content;margin:.25rem 0}math{font-size:1em}@media(forced-colors:active){.guide,.source,header,.target{border-color:CanvasText}.line:target{outline:2px solid Highlight}.warn,.muted,.kicker{color:CanvasText}}"""
(O/'coverage.css').write_text(css+'\n');(O/'mark.svg').write_text('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32"><rect width="32" height="32" rx="4" fill="white"/><path d="M7 6h16v2H9v16h14v2H7z" fill="#194b67"/><path d="M12 11h9v2h-9zm0 5h9v2h-9z" fill="#194b67"/></svg>\n')
modules={p['file']:p['source_sha256'] for p in positions.values() if p.get('file') and p.get('line')}
for f,mhash in sorted(modules.items()):
 src=H/'lean'/f;rawhref='../../lean/'+url(f)
 if not src.is_file():
  src=H/'proof-supplement'/f;rawcopy=checks/f;rawcopy.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,rawcopy);rawhref='../checks/'+url(f)
 assert src.is_file() and sha(src)==mhash;ls=src.read_text().splitlines();m=modid(f)
 # Native scrolling preserves the shape of the proved Lean term. Line numbers are links, not copied text nodes in the code.
 code=''.join('<span class="line" id="L'+str(i)+'"><a class="ln" aria-label="Line '+str(i)+'" href="#L'+str(i)+'">'+str(i)+'</a>'+esc(s)+'\n</span>' for i,s in enumerate(ls,1))
 body='<p class="kicker">Lean source</p><h1><code>'+esc(m)+'</code></h1><p><a href="'+rawhref+'">Open the unaltered Lean file</a> · '+str(len(ls))+' lines</p><pre class="source" tabindex="0" aria-label="Lean source, scroll horizontally if needed"><code>'+code+'</code></pre>'
 (O/'source'/(m+'.html')).write_text(htm(m,body,1))
def label(r):
 generic=(r['kind'].capitalize()+' '+r['printed']).strip()
 if not r['printed'] and r['kind'] in ['prose span','remark']:generic+=' · manuscript line '+r['first_line']
 title=titles[r['source_id']];assert title['source_title']==r['title_tex']
 return esc(generic)+((' · '+title['title_html']) if title['title_html'] else '')
def solblock(y):
 v=providers.get(y['qualified_name'])
 if not v:return ''
 if v.get('verified'):
  links=' · '.join('<a href="'+source_url(p,'../')+'"><code>'+esc(p['name'])+'</code></a>' for p in v['sources'])
  kind='Companion proof' if v.get('from_supplement') else 'Proof term'
  check='WholeSpaceSupplement.lean' if v.get('from_supplement') else 'ProofBindings.lean'
  code='<code>'+esc(v['expression'])+'</code>'
  if v['expression'].startswith('by') or 'hrsReaderEntropyDispatcher' in v['expression']:code='A proof assembled from '+links;links=''
  extra=' The two companion results are outside the frozen base.' if v.get('from_supplement') else ''
  t='<small><strong>'+kind+'.</strong> '+code+'. <a href="../checks/'+check+'">Exact type checked</a>; standard axioms only.'+extra+(' '+links if links else '')+'</small>' 
  return t
 return '<small>'+esc(v['public_note'])+'</small>'
def historical(s):
 if s=='GAP':return 'Earlier record: no verified proof of this declaration.'
 if s.startswith('UNRESOLVED_TOKEN'):return 'Earlier record: no bound declaration.'
 if s.startswith('DEF-ROOT'):
  if 'partial' in s:return 'Reference comparison: some defining bodies or fields were checked directly.'
  if 'L1 tower-only' in s:return 'Reference comparison: only the surrounding declaration dependencies were checked.'
  if 'L2 PASS' in s:return 'Reference comparison checked at least one defining body or field.'
  return 'See the original definition-check entry in the claim table.'
 if 'NOT_IN_PINNED_HEAD' in s:return 'Earlier check: no independent reference-head statement was available.'
 if 'tie' in s.lower():return 'Earlier independent-statement check: a separate proof term was tested.'
 if 'THM-PASS' in s or 'Comparator' in s or 'PASS against' in s:return 'Earlier independent-statement check: a pass was recorded for the claim.'
 return 'Earlier record: '+esc(s)+'.'
def row(x,y):
 n=y['qualified_name']
 if not n:return '<li data-ledger-line="'+x['ledger_line']+'"><code>'+esc(y['token'])+'</code><small>No declaration was bound to this entry.</small></li>'
 r=axi[n];cl=r['classification'];isdef=y['kind']!='theorem'
 badge={'depends on sorryAx':'Uses an admission (sorryAx).','standard axioms only':'Standard axioms only.','axiom free':'Axiom-free.'}[cl]
 lead=('<a href="'+source_url(y,'../')+'"><code>'+esc(n)+'</code></a> · '+esc(y['kind'])+', line '+y['line'])
 if n!=y['token']:lead+='<small>Recorded as <code>'+esc(y['token'])+'</code>; qualification resolved in the source module.</small>'
 note=historical(x['historic_manifest_status'])
 return '<li data-ledger-line="'+x['ledger_line']+'">'+lead+'<small class="record-status '+('warn' if 'sorryAx' in cl else '')+'">'+badge+'</small>'+solblock(y)+'<small>'+note+'</small></li>'
def targetbox(r):
 rs=by[r['source_id']];details='<p>No declaration recorded for this manuscript remark.</p>' if not rs else '<details><summary>'+str(len(rs))+' Lean '+('entry' if len(rs)==1 else 'entries')+'</summary><ol class="records">'+''.join(row(x,y) for x,y in rs)+'</ol></details>'
 return '<article class="target" data-paper-id="'+esc(r['source_id'])+'" id="'+anc(r['source_id'])+'"><h3>'+label(r)+'</h3><p class="muted">Manuscript lines '+r['first_line']+'–'+r['last_line']+'</p>'+details+'</article>'
def sectionlink(x):return '<a href="sections/'+url(x['id'])+'.html">'+esc(section_title(x['id'])+' · '+x['title'])+'</a>'
sections=[x for x in heads if x['kind']=='section']; assert len(sections)==24
for k in sections:
 sid=k['id'];sub=[s for s in heads if s['parent']==sid];subids=[s['id'] for s in sub];s0='<p class="kicker">'+esc(section_title(sid))+'</p><h1>'+esc(k['title'])+'</h1>'
 if sid in ('M-3','M-6','S-S2','S-S3','S-S5'):
  chapter={'M-3':'The-sharp-sub-Coulomb-commutator','M-6':'Mesoscopic-observations-and-screening'}.get(sid,'Whole-space-fluctuations')
  s0+='<p class="guide"><a href="../../reader/'+chapter+'/index.html">Read selected results with their Lean statements and proofs</a>.</p>'
 if sub:s0+='<nav aria-label="Subsections"><h2>In this section</h2><ul class="jump">'+''.join('<li><a href="#'+esc(ss['id'])+'">'+esc(ss['title'])+'</a></li>' for ss in sub)+'</ul></nav>'
 for subid in ['']+subids:
  rs=sorted(paperrows.get((sid,subid),[]),key=lambda r:int(r['first_line']))
  if subid:s0+='<h2 id="'+esc(subid)+'">'+esc(hg[subid]['title'])+'</h2>'
  elif not rs:continue
  else:s0+='<h2>Section opening</h2>'
  s0+=''.join(targetbox(r) for r in rs) if rs else '<p>No separately indexed result begins in this subsection.</p>'
 for r in paperrows.get((sid,'cross'),[]):s0+='<p>Continued from <a href="'+url(r['home'])+'.html#'+anc(r['source_id'])+'">'+label(r)+'</a>.</p>'
 (O/'sections'/(sid+'.html')).write_text(htm(k['title'],s0,1))
index='<p class="kicker">Fluctuations of Riesz gases</p><h1>From the paper to Lean</h1><p>Choose a section of the main paper or the whole-space supplement. Open a result to find the declarations attached to it, then follow a name to the numbered Lean source.</p><p class="guide">For a mathematical statement alongside its Lean formulation, start with the <a href="../reader/index.html">reader</a>. The index below also includes definitions, remarks, and statements with separate proof terms. <a href="evidence.html">How to read the evidence</a>.</p>'
for d,title in [('M','Main paper'),('S','Whole-space supplement')]:
 index+='<h2>'+title+'</h2><ul class="jump">'+''.join('<li>'+sectionlink(k)+'</li>' for k in sections if k['doc']==d)+'</ul>'
(O/'index.html').write_text(htm('From the paper to Lean',index))
ev='<p class="kicker">Paper-to-Lean index</p><h1>Reading the evidence</h1><h2>What a source link says</h2><p>A source link identifies a declaration and its line in the pinned Lean file. A manuscript heading may lead to several results or to no recorded declaration. Some declarations fix the intended statement using <code>sorry</code>; a different Lean term supplies the proof.</p><h2>Axiom reports</h2><p>Lean reports the axioms on which a declaration depends. The standard axioms here are <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code>. A dependency on <code>sorryAx</code> means that this particular term relies on an admission, directly or through another declaration. Where a separate proof has been checked to have exactly the required type, its entry identifies that proof.</p><h2>How many entries?</h2><p>The index covers 24 sections, 143 subsections, 315 named manuscript items and 20 additional passages. Of the 1,182 recorded entries, 1,166 resolve to 1,146 distinct declarations; 16 have no bound module. Separately, 16 manuscript remarks have no recorded entry.</p><p>The axiom inventory includes the 1,146 declarations and five additional reader or provider declarations: 800 use standard axioms only, one is axiom-free, and 350 depend on <code>sorryAx</code>. These are counts of Lean constants, not mathematical results. The axiom inventory was queried on the built package. Earlier independent-statement comparisons and kernel replays have their own scopes.</p><h2>An example</h2><p>For Proposition 6.1, <code>HRS.screening_comparison</code> fixes the statement with <code>sorry</code>. The proof is <code>HRS.screening_comparison_proof</code>, which has the same type and only standard axioms. Main Lemma D.6, <code>HRS.fdl_commutator</code>, remains stated only. The sharp sub-Coulomb theorem in the reader is a different estimate.</p><p><a href="declaration-locators.tsv">Download the declaration locations (TSV)</a> · <a href="current-axioms.tsv">Download the axiom inventory (TSV)</a></p>'
if sum(v.get('verified',False) for v in providers.values())==349 and sum(v.get('from_supplement',False)for v in providers.values())==2:
 ev=ev.replace('<h2>An example</h2>','<h2>Separate proof terms</h2><p>Of those 350 declarations, 347 have a separate proof expression in the frozen package. Lean checked the full type of each expression and reported only standard axioms. Two further proofs, for Supplement Proposition S11.1 and Corollary S11.2, are in the accompanying proof supplement: 31 original modules compiled against the unchanged base. Main Lemma D.6 remains stated only.</p><p><a href="checks/ProofBindings.lean">The 347 type checks</a> · <a href="checks/WholeSpaceSupplement.lean">The two companion type checks</a></p><h2>An example</h2>')
(O/'evidence.html').write_text(htm('Reading the evidence',ev))
print(json.dumps(dict(sections=len(sections),subsections=len(heads)-len(sections),targets=len(targets),ledger_rows=len(loc),source_files=len(modules),providers=len(providers),files=sum(f.is_file()for f in O.rglob('*')),output_bytes=sum(p.stat().st_size for p in O.rglob('*')if p.is_file()))))
