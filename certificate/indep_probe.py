# Independent re-implementation of the certificate check, using exact rationals / big-int 2-adic arithmetic.
import sys, itertools, array, random
from fractions import Fraction
s=int(sys.argv[1]); H=int(sys.argv[2]); SLACK=int(sys.argv[3]); vf=sys.argv[4]
S=1<<s; BIG=1<<(3*s+80)
# chains: pick k distinct alphas and k distinct gammas, pair sorted-with-sorted
chains={}
for k in range(0,min(s,H)+1):
    for al in itertools.combinations(range(s),k):
        for ga in itertools.combinations(range(H),k):
            vfull=sum(pow(7,-g,BIG)<<a for a,g in zip(al,ga))%BIG
            h=(ga[-1]+1) if k else 0
            chains.setdefault(vfull%S,[]).append((vfull,h))
assert len(chains)==S
for c in chains:
    m=min(h for _,h in chains[c]); chains[c]=[x for x in chains[c] if x[1]<=m+SLACK]
V=array.array('f'); V.frombytes(open(vf,'rb').read())
SC=1<<20
import math
Vi=[(math.floor(float(x)*SC+0.5) if x>=0 else -math.floor(-float(x)*SC+0.5)) for x in V]
ties=sum(1 for x in V if (float(x)*SC)%1==0.5)
print("half-ties:",ties)
def Vr(c,b): return Vi[c*S+b]

import re
states=[int(x) for x in sys.argv[5].split(",")]
rng=random.Random(1)
for x in states:
    c=x>>s; b1=x&(S-1); tot=0
    for u in range(S):
        hi=rng.getrandbits(60)
        z=c+(b1<<s)+(u<<(2*s))+(hi<<(3*s))
        best=None
        for vfull,h in chains[c]:
            zn=((z-vfull)%BIG)//S * pow(7,h,BIG) % BIG
            cp=zn%S; bp=(zn>>s)%S
            val=h*SC+Vr(cp,bp)
            if best is None or val<best: best=val
        tot+=best
    print("indep state",x,"d=",tot-S*Vr(c,b1)); sys.stdout.flush()
