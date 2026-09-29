# Validate the exact 2-look transition formula against direct 2-adic arithmetic, s small.
import random
s=6; H=7; S=1<<s; MS=S-1; L=3*s+64; MODL=1<<(L+3*s)
pinv=pow(7,-1,1<<200)
def u7(g,mod): return pow(pinv,g,mod)
chains=[]
def gen(a0,g0,terms):
    chains.append(list(terms))
    for a in range(a0,s):
        for g in range(g0,H):
            gen(a+1,g+1,terms+[(a,g)])
gen(0,0,[])
def val(terms,mod): return sum((u7(g,mod)<<a) for a,g in terms)%mod
bad=0; tests=0
for trial in range(3000):
    z=random.getrandbits(L)
    c=z&MS; b1=(z>>s)&MS; u=(z>>(2*s))&MS
    cands=[t for t in chains if val(t,S)==c]
    for t in random.sample(cands,min(5,len(cands))):
        h=(max(g for a,g in t)+1) if t else 0
        v=val(t,1<<(3*s)); k1=(v>>s)&MS; k2=(v>>(2*s))&MS
        d1=(b1-k1)&MS; borrow=1 if b1<k1 else 0; prod=(7**h)*d1; cp=prod&MS; q1=prod>>s
        b2=((7**h)*((u-k2-borrow)%S)+q1)&MS
        # direct: z_next = 7^h (z - v_full)/2^s  (2-adic, mod large)
        vf=val(t,MODL); zn=((z-vf)%MODL)>>s; zn=(zn*(7**h))%(MODL>>s)
        dc=zn&MS; db2=(zn>>s)&MS
        tests+=1
        if (dc,db2)!=(cp,b2): bad+=1
print("tests",tests,"mismatches",bad)
