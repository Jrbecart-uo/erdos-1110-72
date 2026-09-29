# End-to-end simulation of the certified encoding for (7,2), s=11: random y -> explicit representation n.
import random, math, sys, array
s=11; H=10; SLACK=3; S=1<<s; MS=S-1; M3=1<<(3*s)
inv7=pow(7,-1,1<<64)
u7=[pow(inv7,g,M3) for g in range(H+1)]
# chains (same definition as verify.c): list of (alpha,gamma) strictly increasing, alpha<s, gamma<H
chains={}
def gen(a0,g0,terms,v):
    c=v&MS; chains.setdefault(c,[]).append((tuple(terms),v, (terms[-1][1]+1) if terms else 0))
    for a in range(a0,s):
        for g in range(g0,H):
            gen(a+1,g+1,terms+[(a,g)],(v+((u7[g]<<a)%M3))%M3)
sys.setrecursionlimit(10000)
gen(0,0,[],0)
for c in chains:
    mh=min(h for _,_,h in chains[c]); chains[c]=[x for x in chains[c] if x[2]<=mh+SLACK]
Va=array.array("f"); Va.frombytes(open("V_s11_it8.bin","rb").read()); Vi=[int(round(float(x)*(1<<20))) for x in Va]
lam=s*26/73
def run(N,seed):
    rnd=random.Random(seed); L=s*N; y=rnd.getrandbits(L)
    MODZ=1<<(L+3*s)
    z=y; G=0; terms=[]; E_hist=[]
    for t in range(N):
        c=z&MS; b1=(z>>s)&MS; u=(z>>(2*s))&MS
        cand=chains[c]
        if t<N-2:
            best=None
            for (tm,v,h) in cand:
                w=(((c|(b1<<s)|(u<<(2*s)))-v)%M3)>>s; zn=(pow(7,h)*w)%(1<<(2*s))
                val=h*(1<<20)+int(Vi[((zn&MS)<<s)|(zn>>s)])
                if best is None or val<best[0]: best=(val,tm,v,h)
            _,tm,v,h=best
        else:
            tm,v,h=min(cand,key=lambda x:x[2])
        Lnext=math.ceil((t+1)*lam)
        Gn=max(G+h,Lnext)
        terms.append((t,G,tm))
        # exact 2-adic update of full residual
        vfull=sum((pow(7,-g,MODZ)<<a) for a,g in tm)%MODZ
        z=(((z-vfull)%MODZ)>>s)*pow(7,Gn-G,MODZ>>s)%(MODZ>>s)
        G=Gn; E_hist.append(G-Lnext)
    return y,terms,G,E_hist
fails=0; maxE=0; samples=int(sys.argv[1]); N=int(sys.argv[2])
for sd in range(samples):
    y,terms,G,E=run(N,sd)
    A=G  # smallest admissible A for this sample (so every exponent is >= 0); check antichain + congruence
    pairs=[]
    for t,Gt,tm in terms:
        for a_,g in tm: pairs.append((A-Gt-g, s*t+a_))   # (7-exponent, 2-exponent)
    assert all(a>=0 for a,b in pairs)
    # antichain: sort by 2-exponent; 7-exponent must strictly decrease
    pairs.sort(key=lambda x:x[1])
    ok=all(pairs[i][1]<pairs[i+1][1] and pairs[i][0]>pairs[i+1][0] for i in range(len(pairs)-1))
    n=sum(7**a*2**b for a,b in pairs)
    cong=(n - pow(7,A)*y)%(1<<(s*N))==0
    if not(ok and cong): fails+=1
    maxE=max(maxE,max(E))
print(f"samples={samples} N={N} blocks: antichain+congruence failures={fails}; max excess E over run={maxE}; final/line ~ G_N-L_N")

# ---- debug one sample
y,terms,G,E=run(8,1)
A=G
pairs=[]
for t,Gt,tm in terms:
    for a_,g in tm: pairs.append((A-Gt-g, s*t+a_))
pairs.sort(key=lambda x:x[1])
bad=[(pairs[i],pairs[i+1]) for i in range(len(pairs)-1) if not(pairs[i][1]<pairs[i+1][1] and pairs[i][0]>pairs[i+1][0])]
print("antichain violations:",bad[:5])
n=sum(7**a*2**b for a,b in pairs)
print("cong ok:",(n-pow(7,A)*y)%(1<<(s*8))==0)
# check per-block: reconstruct y from blocks
MOD=1<<(s*8)
acc=sum((pow(7,-Gt,MOD)* sum(pow(7,-g,MOD)<<a_ for a_,g in tm) <<(s*t)) for t,Gt,tm in terms)%MOD
print("sum 2^{st}7^{-G_t}v_t == y mod 2^{sN}:", acc==y%MOD)
