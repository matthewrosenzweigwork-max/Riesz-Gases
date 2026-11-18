# Check that every non-'sorry' line of the spec file (at base rev) appears, in order, in the new file.
import sys,subprocess
repo,base,head,path=sys.argv[1:5]
old=subprocess.run(['git','-C',repo,'show',f'{base}:{path}'],capture_output=True,text=True).stdout.split('\n')
new=subprocess.run(['git','-C',repo,'show',f'{head}:{path}'],capture_output=True,text=True).stdout.split('\n')
j=0;missing=[]
for l in old:
    if l.strip() in ('sorry','by sorry'): continue
    l=l.replace(' := by',' :=') if l.endswith(' := by') else l
    while j<len(new) and new[j]!=l and not (l.endswith(' :=') and new[j].startswith(l)): j+=1
    if j==len(new): missing.append(l); j=0; continue
    j+=1
print(path, 'OK' if not missing else 'CHANGED:'); [print('  ',m) for m in missing[:20]]
