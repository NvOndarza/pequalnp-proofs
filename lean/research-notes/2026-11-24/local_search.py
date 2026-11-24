"""Bounded exact local-neighbourhood search for L-meta-2625.
Boundary is taken literally from the desk. Absence in this neighbourhood is not
a lower bound and does not exhaust arbitrary 63-gate circuits.
"""
import json,hashlib,time
from pathlib import Path
BASE=Path(__file__).parent
PATTERNS=[(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
D=[0,1,3,9]
cases=[]
for r in range(13):
 for d in D: cases.append(((1<<((r+d)%13))|(1<<(13+r)),True))
for l,r in PATTERNS:
 for a in [1,3,9]:
  for b in range(13):
   for swap in [False,True]:
    bits=0
    for v in range(13):
     k=(-a*v-b)%13 if swap else (a*v+b)%13
     p,q=(r,l) if swap else (l,r)
     bits|=((p>>k)&1)<<v
     bits|=((q>>k)&1)<<(13+v)
    cases.append((bits,False))
W=len(cases);MASK=(1<<W)-1
inputs=[sum(((x>>i)&1)<<j for j,(x,y) in enumerate(cases)) for i in range(26)]
target=sum(int(y)<<j for j,(x,y) in enumerate(cases))
gates=[]
def add(a,b,op):
 gates.append([a,b,op]);return 26+len(gates)-1
rows=[]
for r in range(13):
 leaves=[(r+d)%13 for d in D]
 x=leaves[0]
 for y in leaves[1:]: x=add(x,y,'or')
 rows.append(add(x,13+r,'and'))
out=rows[0]
for r in rows[1:]:out=add(out,r,'or')
def evaluate(gs,ins=inputs):
 w=list(ins)
 for a,b,op in gs:w.append((w[a]&w[b]) if op=='and' else (w[a]|w[b]))
 return w
w=evaluate(gates)
assert len(gates)==64 and out==89 and w[-1]==target
uses={i:[] for i in range(90)}
for j,(a,b,_) in enumerate(gates):
 uses[a].append(j);uses[b].append(j)
tried=0;found=None;start=time.monotonic()
# Replace a sole-use child and its parent by one arbitrary binary gate.
# Reuse the child's slot (the old child is dead); downstream gate count is63.
# Search operands available before the parent, excluding the removed child.
for parent,(pa,pb,pop) in enumerate(gates):
 for childwire in [pa,pb]:
  if childwire<26:continue
  child=childwire-26
  if uses[childwire]!=[parent]:continue
  available=[v for v in range(26+parent) if v!=childwire]
  for ai,a in enumerate(available):
   for b in available[ai:]:
    for op in ['and','or']:
     tried+=1
     values=list(w[:26+parent])
     values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
     for ca,cb,co in gates[parent+1:]:
      values.append(values[ca]&values[cb] if co=='and' else values[ca]|values[cb])
     if values[-1]!=target:continue
     # Remove now-unused child physically and reindex every live wire.
     repl=[g[:] for g in gates];repl[parent]=[a,b,op]
     repl.pop(child)
     repl=[[u-1 if u>childwire else u,v-1 if v>childwire else v,o] for u,v,o in repl]
     assert len(repl)==63 and evaluate(repl)[-1]==target
     found={'child':child,'parent':parent,'replacement':[a,b,op],'gates':repl};break
    if found:break
   if found:break
  if found:break
 if found:break
result={'gap':'L-meta-2625','cases':W,'unique_cases':len(set(cases)),'baseline_gates':64,'contractions_tested':tried,'seconds':time.monotonic()-start,'candidate':found,'scope':'sole-use child/parent contractions only, not arbitrary circuit exhaustion','program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(BASE/'local-search-result.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
