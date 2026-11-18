#!/usr/bin/env python3
"""Compile the 31 companion modules and check the two restored proof terms. Never writes to the base cache."""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path as P
q=argparse.ArgumentParser()
q.add_argument('--base',required=True,type=P,help='Already built, unchanged HRS lean/ checkout')
q.add_argument('--lean',required=True,type=P,help='Pinned Lean executable, version 4.34.1')
q.add_argument('--output',required=True,type=P,help='Fresh build directory outside both inputs')
q.add_argument('--check-inputs',action='store_true',help='Verify the source and pins, without creating output or compiling.')
a=q.parse_args();s=P(__file__).resolve().parent;b=a.base.resolve();o=a.output.resolve();exe=a.lean.resolve();r=json.loads((s/'INPUTS.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not any(o.is_relative_to(p)for p in [s,b]) and not o.exists(),'Choose a fresh path outside inputs'
assert sha(b/'lake-manifest.json')==r['base_manifest_sha256'] and sha(b/'lean-toolchain')==r['base_toolchain_sha256'] and 'version 4.34.1' in subprocess.check_output([str(exe),'--version'],text=True)
for m,v in r['modules'].items():assert sha(s/v['path'])==v['source_sha256'],m
bl=b/'.lake/build/lib/lean'
for m,h in r['retained_source_sha256'].items():
 f=m.replace('.','/');assert sha(b/(f+'.lean'))==h and (bl/(f+'.olean')).is_file(),m
assert sha(s/'ExactTypes.lean')==r['probe_sha256']
if a.check_inputs:print('Source, pinned manifests and required base cache locations match.');raise SystemExit(0)
o.mkdir(parents=True);lib=o/'lib';lib.mkdir();log=o/'logs';log.mkdir();mask={v['path'][:-5]for v in r['modules'].values()};dirs={q.as_posix() for v in mask for q in P(v).parents}
def layer(rel):
 dst=lib/rel;dst.mkdir(exist_ok=True,parents=True)
 for x in (bl/rel).iterdir():
  rp=(P(rel)/x.name).as_posix()
  if x.is_dir() and rp in dirs:layer(rp)
  elif not any(rp==m or rp.startswith(m+'.')for m in mask):(lib/rp).symlink_to(x.resolve(),target_is_directory=x.is_dir())
layer('.');env=dict(os.environ);env['LEAN_NUM_THREADS']='1';env['LEAN_PATH']=os.pathsep.join([str(lib),str(bl)]+[str(x/'.lake/build/lib/lean')for x in sorted((b/'.lake/packages').iterdir())]);done={};remaining=set(r['modules']);t=time.monotonic()
def run(n,src,compile):
 stem=src[:-5];ole=lib/(stem+'.olean');il=lib/(stem+'.ilean')
 if compile:
  ole.parent.mkdir(parents=True,exist_ok=True);assert not ole.exists() and not ole.is_symlink() and not il.exists() and not il.is_symlink() and ole.resolve().is_relative_to(lib)
 cmd=[str(exe),'-j1']+(['-o',str(ole),'-i',str(il)] if compile else [])+[src]
 with (log/(n+'.out')).open('xb') as z, (log/(n+'.err')).open('xb') as e:
  proc=subprocess.run(cmd,cwd=s,env=env,stdin=subprocess.DEVNULL,stdout=z,stderr=e,timeout=1800)
 if proc.returncode:raise SystemExit('Lean failed for '+n+'; inspect its log; the base package was not changed.')
 return sha(ole) if compile else None
while remaining:
 ready=sorted(n for n in remaining if all(x in done or x not in r['modules']for x in r['modules'][n]['imports']))
 assert ready,'cycle'
 for n in ready:done[n]=run(n,r['modules'][n]['path'],True);remaining.remove(n);print(n,flush=True)
run('ExactTypes','ExactTypes.lean',False);out=(log/'ExactTypes.out').read_text();assert all("'HRSReleaseOverlay."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in out for n in ['r2_tensor_relaxation','r2_two_parameter_edgeworth'])
(o/'receipt.json').write_text(json.dumps({'status':'PASS','compiled_module_sha256':done,'probe_stdout_sha256':sha(log/'ExactTypes.out'),'seconds':round(time.monotonic()-t,2),'scope':'31 added source modules, two exact provider types, prebuilt base and pinned dependencies. No clean base rebuild or independent Comparator.'},indent=2)+'\n');print('PASS: 31 modules and two exact proof terms.')
