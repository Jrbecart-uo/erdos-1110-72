# Exhaustive checks at s=4: (a) u_t uniform & independent given y mod 2^{s(t+2)} under the padded look-ahead policy;
# (b) unpadded steps: realized X_{t+1} == certificate's next(x,u,C); (c) injectivity + antichain + exponents for fixed A.
import itertools, array, math
from collections import defaultdict
s=3;H=5;SLACK=3;S=1<<s;M3=1<<(3*s);N=4
BIG=1<<(s*N+3*s+40)
chains={}
for k in range(0,min(s,H)+1):
  for al in itertools.combinations(range(s),k):
    for ga in itertools.combinations(range(H),k):
      v=sum(pow(7,-g,BIG)<<a for a,g in zip(al,ga))%BIG; h=(ga[-1]+1) if k else 0
      chains.setdefault(v%S,[]).append((tuple(zip(al,ga)),v,h))
for c in chains:
  m=min(x[2] for x in chains[c]); chains[c]=[x for x in chains[c] if x[2]<=m+SLACK]
V=array.array('f'); V.frombytes(open('Vs3.bin','rb').read()); Vi=[math.floor(x*2**20+0.5) for x in V]
lam=s*26/73
def nxt(z3,v,h):
  zn=((z3-v)%M3)>>s; zn=(7**h*zn)%(S*S); return zn%S, zn>>s
def run(y,Nb,lookahead_to):
  z=y; G=0; hist=[]; MOD=BIG
  for t in range(Nb):
    c=z%S; b1=(z>>s)%S; u=(z>>(2*s))%S
    if t<lookahead_to:
      best=min(chains[c], key=lambda ch:(ch[2]*2**20+Vi[(lambda p:p[0]*S+p[1])(nxt(z%M3,ch[1],ch[2]))], ch[0]))
    else: best=min(chains[c],key=lambda ch:(ch[2],ch[0]))
    tm,v,h=best
    Gn=max(G+h, math.ceil((t+1)*lam)); padded=Gn>G+h
    pred=nxt(z%M3,v,h)
    z=(((z-v)%MOD)>>s)*pow(7,Gn-G,MOD)%MOD; MOD>>=s
    hist.append((t,G,tm,c,b1,u,padded,pred,(z%S,(z>>s)%S)))
    G=Gn
  return hist,G
# (a)+(b): y ranges over all residues mod 2^{s*(N+2)} (so look-ahead defined for all N blocks)
L=s*(N+2); groups=defaultdict(lambda: defaultdict(int)); mism=0; unp=0
for y in range(1<<L):
  hist,G=run(y,N,N)
  for (t,Gt,tm,c,b1,u,padded,pred,real) in hist:
    if not padded:
      unp+=1
      if pred!=real: mism+=1
    if t<=N-1:
      groups[(t, y%(1<<(s*(t+2))))][u]+=1
bad=0
for key,d in groups.items():
  t=key[0]; per=1<<(L-s*(t+2)-s)
  if len(d)!=S or any(cnt!=per for cnt in d.values()): bad+=1
print("groups",len(groups),"non-uniform groups",bad,"unpadded steps",unp,"pred mismatches",mism)
# (c) injectivity etc for y mod 2^{sN}, last two blocks min-height, A = max G_N over all y
res=[]
for y in range(1<<(s*N)):
  hist,G=run(y,N,N-2); res.append((y,hist,G))
A=max(G for _,_,G in res)
ns=set(); ok=True
for y,hist,G in res:
  pairs=[(A-Gt-g, s*t+a) for (t,Gt,tm,*_) in hist for (a,g) in tm]
  assert all(e>=0 for e,_ in pairs)
  pairs.sort(key=lambda p:p[1])
  if not all(pairs[i][1]<pairs[i+1][1] and pairs[i][0]>pairs[i+1][0] for i in range(len(pairs)-1)): ok=False
  n=sum(7**a*2**b for a,b in pairs)
  if (n-7**A*y)%(1<<(s*N)): ok=False
  ns.add(n)
print("A",A,"antichain+congruence ok",ok,"distinct n",len(ns),"of",1<<(s*N),"zero present",0 in ns)
