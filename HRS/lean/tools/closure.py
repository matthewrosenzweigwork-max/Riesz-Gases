import sys,re,os
root=sys.argv[1]; start=sys.argv[2:]
seen=set(); st=list(start)
while st:
    m=st.pop()
    if m in seen: continue
    p=os.path.join(root,m.replace('.','/')+'.lean')
    if not os.path.exists(p):
        continue
    seen.add(m)
    for l in open(p):
        mm=re.match(r'\s*import\s+(DGRHS\S*)',l)
        if mm: st.append(mm.group(1))
print(len(seen))
for m in sorted(seen): print(m)
