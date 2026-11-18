#!/usr/bin/env python3
"""Offline, cache-seeded, documentation-only raw renderer. Never runs lake build/update."""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,time,signal,re
P=pathlib.Path
HERE=P(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--renderer-root',type=P,required=True)
parser.add_argument('--hrs-root',type=P,required=True)
parser.add_argument('--lean',type=P,required=True,help='Already installed pinned Lean executable; no elan download')
parser.add_argument('--output',type=P,required=True,help='New empty directory outside source roots')
parser.add_argument('--timeout-seconds',type=int,default=300,help='Per doc/render step timeout, 1..1800 seconds')
parser.add_argument('--trace',action='store_true',help='strace file/network operations; needs strace installed')
parser.add_argument('--seed-docs-from',type=P,help='Prior successful receipt-bound six-module doc build; compile extras only')
parser.add_argument('--docs-root',type=P,default=HERE,help='Optional private candidate directory; original six must match staged baseline')
parser.add_argument('--extra-module',action='append',default=[],help='Additional module basename, repeated in dependency order after baseline six')
parser.add_argument('--entry-module',default='Main',help='Render this compiled module; default Main')
a=parser.parse_args();R=a.renderer_root.resolve();H=a.hrs_root.resolve();lean=a.lean.resolve();out=a.output.resolve()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,cwd=None):return subprocess.check_output(args,cwd=cwd,text=True).strip()
def need(ok,msg):
 if not ok:raise SystemExit(msg)
lock=json.loads((HERE/'RAW-BUILD-LOCK.json').read_text());pins=json.loads((HERE/'RENDERER-PINS.json').read_text())
need(1<=a.timeout_seconds<=1800,'Timeout must be 1..1800 seconds')
D=a.docs_root.resolve()
need(all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',m) for m in a.extra_module+[a.entry_module]),'Only simple module basenames supported')
need(not out.exists(),'Output must not exist; preserve prior evidence')
need(not any(out.is_relative_to(p) for p in [HERE,D,R,H]),'Output must be outside source/dependency roots')
need(lean.is_file(),'Missing preinstalled Lean executable')
need('version 4.34.1' in run([str(lean),'--version']),'Wrong Lean version')
need((HERE/'lean-toolchain').read_text().strip()==pins['lean'],'Staged toolchain pin differs')
for root,key in [(R,'renderer'),(H,'hrs')]:
 need((root/'lean-toolchain').read_text().strip()==pins['lean'],f'{key} toolchain differs')
 need(sha(root/'lake-manifest.json')==lock[key+'_manifest_sha256'],f'{key} manifest differs')
if run(['git','rev-parse','HEAD'],R)!=pins['verso_blueprint_commit']:raise SystemExit('Renderer HEAD differs')
need(not run(['git','status','--porcelain','--untracked-files=no'],R),'Renderer tracked worktree dirty')
checks=[]
for root,key in [(R,'renderer'),(H,'hrs')]:
 manifest=json.loads((root/'lake-manifest.json').read_text())
 for pkg in manifest['packages']:
  if pkg.get('type')!='git':raise SystemExit('Unimplemented non-git package verification: '+pkg['name'])
  d=root/'.lake/packages'/pkg['name'].removeprefix('«').removesuffix('»');head=run(['git','rev-parse','HEAD'],d)
  need(head==pkg['rev'],f'{key}/{pkg["name"]} HEAD mismatch')
  need(not run(['git','status','--porcelain','--untracked-files=no'],d),f'{key}/{pkg["name"]} tracked files modified')
  checks.append({'root':key,'name':pkg['name'],'rev':head})
need(run(['git','rev-parse','HEAD'],R/'.lake/packages/verso')==pins['verso_commit'],'Verso pin differs')
need(run(['git','rev-parse','HEAD'],H/'.lake/packages/mathlib')==pins['mathlib_commit'],'mathlib pin differs')
# Only existing compiled library directories; never invoke Lake or compile an HRS module.
libs=[]
for root in [R,H]:
 libs += [d/'.lake/build/lib/lean' for d in sorted((root/'.lake/packages').iterdir()) if (d/'.lake/build/lib/lean').is_dir()]
 libs.append(root/'.lake/build/lib/lean')
need(all(p.is_dir() for p in libs),'Missing compiled library cache')
need((R/'.lake/build/lib/lean/VersoBlueprint.olean').is_file(),'Missing renderer cache')
need((H/'.lake/build/lib/lean/HRS/Sections/Sec6.olean').is_file(),'Missing HRS cache')
out.mkdir(parents=True);docs=out/'docs';docs.mkdir();shutil.copy2(HERE/'lean-toolchain',docs/'lean-toolchain')
baseline=['PaperIndex','Commutator','Screening','Evidence','Contents','Main']
for m in baseline:need(sha(D/(m+'.lean'))==sha(HERE/(m+'.lean')),'Candidate changed baseline module '+m)
need(not set(baseline).intersection(a.extra_module),'Extra module shadows baseline')
need(len(set(a.extra_module))==len(a.extra_module),'Duplicate extra module')
modules=baseline+a.extra_module
need(a.entry_module in modules,'Entry module was not compiled')
for m in modules:shutil.copy2(D/(m+'.lean'),docs/(m+'.lean'))
seeded=[]
if a.seed_docs_from:
 prior=a.seed_docs_from.resolve();old=json.loads((prior/'raw-build-receipt.json').read_text())
 need(old.get('status')=='raw-render-complete','Doc seed did not finish raw render')
 for m in baseline:
  need(old['docs_before'][m]==sha(docs/(m+'.lean')),'Doc seed source mismatch '+m)
  compiled=prior/'docs'/(m+'.olean')
  need(old['compiled_docs'][m]==sha(compiled),'Doc seed olean mismatch '+m)
  shutil.copy2(compiled,docs/(m+'.olean'));seeded.append(m)
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[docs,*libs,lean.parent.parent/'lib/lean']))
env.pop('LEAN_SRC_PATH',None)
receipt={'seeded_doc_modules':seeded,'driver_sha256':sha(P(__file__)), 'entry_module':a.entry_module,'mode':'cache-seeded doc-only; NOT cold build','lean_version':run([str(lean),'--version']),'dependency_pins':checks,'docs_before':{m:sha(docs/(m+'.lean')) for m in modules},'steps':[],'status':'running'}
def save():(out/'raw-build-receipt.json').write_text(json.dumps(receipt,indent=2))
def step(name,args):
 start=time.monotonic();cmd=['nice','-n','10',*args]
 if a.trace:cmd=['strace','-f','-qq','-e','trace=%file,%network','-o',str(out/(name+'.strace')),*cmd]
 with (out/(name+'.log')).open('w') as log:
  proc=subprocess.Popen(cmd,cwd=docs,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:code=proc.wait(timeout=a.timeout_seconds)
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124
 receipt['steps'].append({'name':name,'returncode':code,'seconds':round(time.monotonic()-start,2)})
 if code:receipt['status']='failed:'+name
 save();need(code==0,'Step failed: '+name+'; inspect log')
save()
for m in modules:
 if m not in seeded:step('compile-'+m,[str(lean),'-j1','-o',m+'.olean',m+'.lean'])
receipt['compiled_docs']={m:sha(docs/(m+'.olean')) for m in modules};save()
step('render',[str(lean),'-j1','--run',a.entry_module+'.lean','--output',str(out/'raw-output')])
receipt['docs_after']={m:sha(docs/(m+'.lean')) for m in modules};need(receipt['docs_after']==receipt['docs_before'],'Docs changed during build')
receipt['status']='raw-render-complete';receipt['raw_files']={str(p.relative_to(out/'raw-output')):sha(p) for p in (out/'raw-output').rglob('*') if p.is_file()};save()
print('Raw native output:',out/'raw-output');print('Not the accepted postprocessed/share-safe reader. Do not publish raw output.')
