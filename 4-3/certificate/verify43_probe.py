# Independent big-integer spot check of a (B,Q,s,D) potential certificate with dead states.
# Uses: V table (float32, gvid transposed layout), the viable set W dumped by verifyd (bitset),
# and re-derives everything else with Python integers:
#   chains via itertools (alpha-set, gamma-set of equal size, paired in order), values with pow(Q,-g,mod),
#   transitions next = Q^h ((z - v) / B^s) mod B^D computed on z with RANDOM high digits above D+s
#   (they must not matter), closure (every u has a kept chain into W; Q*x in W) and the drift value
#   d(x) = sum_u min_{C: next in W} (h*2^20 + Vi(next)) - B^s Vi(x), printed per sampled state.
import sys, itertools, array, random, math
B,Q,s,D,H,SLACK = map(int, sys.argv[1:7]); vf, wf, nsamp = sys.argv[7], sys.argv[8], int(sys.argv[9])
P = B**s; MD = B**D; MDm = MD // P; BIG = B**(D+s+40)
chains = {}
for k in range(0, min(s,H)+1):
    for al in itertools.combinations(range(s), k):
        for ga in itertools.combinations(range(H), k):
            v = sum(pow(Q, -g, BIG) * B**a for a, g in zip(al, ga)) % BIG
            h = (ga[-1] + 1) if k else 0
            chains.setdefault(v % P, []).append((v, h))
for c in chains:
    m = min(h for _, h in chains[c]); chains[c] = [x for x in chains[c] if x[1] <= m + SLACK]
V = array.array('f'); V.frombytes(open(vf, 'rb').read()); assert len(V) == MD
Wb = open(wf, 'rb').read()
def inW(x): return (Wb[x >> 3] >> (x & 7)) & 1
SC = 1 << 20
def Vi(x):
    d = float(V[(x % MDm) * P + x // MDm]) * SC
    return int(math.floor(abs(d) + 0.5)) * (1 if d >= 0 else -1)
rng = random.Random(int(sys.argv[10]) if len(sys.argv) > 10 else 1)
Ws = []
while len(Ws) < nsamp:
    x = rng.randrange(MD)
    if inW(x): Ws.append(x)
out = []
for x in Ws:
    c = x % P; tot = 0
    assert inW((Q * x) % MD), "Q-closure fails"
    for u in range(P):
        hi = rng.getrandbits(80)
        z = x + MD * u + (B**(D+s)) * hi
        best = None
        for v, h in chains.get(c, []):
            r = (z - v) % BIG; assert r % P == 0
            nx = (pow(Q, h) * (r // P)) % MD
            if not inW(nx): continue
            val = h * SC + Vi(nx)
            if best is None or val < best: best = val
        assert best is not None, "closure fails at state %d u=%d" % (x, u)
        tot += best
    out.append((x, tot - P * Vi(x)))
for x, d in out: print("indep state", x, "d=", d)
print("max d over sample:", max(d for _, d in out), " ghat-sample:", max(d for _, d in out) / (P * SC))
