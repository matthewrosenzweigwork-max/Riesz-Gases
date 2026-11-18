/* Read-only smoke test of the shipped native full-text engine and all result snippets. */
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
const base=path.resolve(process.argv[2]||'../../reader','-verso-search');
const w={},ctx={window:w,elasticlunr:require(path.join(base,'elasticlunr.min.js'))};
vm.createContext(ctx);vm.runInContext(fs.readFileSync(path.join(base,'searchIndex.js'),'utf8'),ctx);
assert.equal(typeof w.searchIndex.search,'function');assert.ok(/^[a-f0-9]+$/.test(w.searchIndexVersion));
const docs=w.searchIndex.documentStore.docs;assert.equal(Object.keys(docs).length,104);
const buckets=new Map();
for(const id of Object.keys(docs)){
 const k=Array.from(Buffer.from(id)).reduce((a,b)=>(a+b)%256,0);
 if(!buckets.has(k)){
  const filename='searchIndex_'+k+'.'+w.searchIndexVersion+'.js';
  w.docContents[k]={resolve:v=>buckets.set(k,v)};
  vm.runInContext(fs.readFileSync(path.join(base,filename),'utf8'),ctx);
 }
 assert.ok(buckets.get(k)[id] && typeof buckets.get(k)[id].contents==='string',id);
}
const qs=[
 ['tensor relaxation','/Relaxation-on-moving-windows/#s11-tensor-relaxation'],
 ['stationary first correction','/Relaxation-on-moving-windows/#s11-two-parameter-edgeworth'],
 ['S11.1','/Relaxation-on-moving-windows/#s11-tensor-relaxation'],
 ['S11.2','/Relaxation-on-moving-windows/#s11-two-parameter-edgeworth'],
 ['expected cubic pairing','/Relaxation-on-moving-windows/#s11-expected-cubic-pairing'],
 ['screening','/Mesoscopic-observations-and-screening/#screening'],
 ['whole-space fluctuations','/Whole-space-fluctuations/#whole-space-headlines']
];
const rank={};
for(const [q,id] of qs){
 const res=w.searchIndex.search(q,{expand:true,bool:'AND',fields:{header:{boost:1.25},contents:{boost:1}}});
 const pos=res.findIndex(x=>x.ref===id);rank[q]=pos<0?null:pos+1;assert.ok(pos>=0,[q,res.slice(0,3).map(x=>x.ref)].join(':'));
}
console.log(JSON.stringify({nativeFullTextQueries:rank,searchDestinations:Object.keys(docs).length,searchShardBuckets:buckets.size,source:'Vendored native search index and Elasticlunr engine. Ranks shown before fuzzy-search merging.'},null,2));
