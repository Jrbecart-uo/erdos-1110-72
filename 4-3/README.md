# Integers representable by $\lbrace 4,3\rbrace$-antichains have positive lower density

*Jean-Roch Bécart, using Claude Opus 5.5 (Anthropic) via Claude Code. Draft, 2026-09-29.*

*Status: computer-assisted proof. The reduction "certificate ⇒ positive lower density" is formalized in Lean 4 /
Mathlib for general bases (`lean/E1110G.lean`, no `sorry`, standard axioms only). The finite certificate
(2^28 states) is checked by an exact C program and spot-checked by an independent Python big-integer program;
it is not checked in Lean. The proof, programs and Lean code were produced by the AI under the author's
direction; not yet reviewed by a human expert.*

## 1. Statement

For coprime $p>q\ge2$, call $n$ representable if $n=\sum_i p^{a_i}q^{b_i}$ with no summand dividing another
(Erdős problem #1110). Yu and Chen proved that the representable integers have density zero when $q>3$, or
$q=3,\ p>6$, or $q=2,\ p>10$. The remaining pairs are $(5,2),(7,2),(9,2),(4,3),(5,3)$. Positive lower density
has been claimed for $(5,2)$ (Ding–Li–Liu–Zhang, Aug. 2026) and for $(7,2)$ (our earlier note).

**Theorem.** For $(p,q)=(4,3)$ the representable integers have positive lower density.

$(4,3)$ has congruence obstructions. At most one summand $4^a$ has no factor 3, and $4^a\equiv1\pmod 3$, so
$n\not\equiv2\pmod 3$. Likewise at most one summand $3^b$ has no factor 4, and $3^b\equiv\pm1\pmod 4$, so
$n\not\equiv2\pmod4$. These obstructions recur at every scale of the construction, which is why the $(7,2)$
argument must be extended.

## 2. The general criterion (Theorem A′)

Let $b,r\ge2$ be coprime, the digit base and the other base. For $(4,3)$ we take $b=4$ and $r=3$. Terms are
$r^{k}b^{l}$ and representability is symmetric in the two bases. Fix a block length of $s$ digits, $P=b^s$, a
state length of $D$ digits and a height bound $H$.

A *chain* is a finite set $\lbrace(\alpha_i,\gamma_i)\rbrace$ with $\alpha$ and $\gamma$ strictly increasing together,
$\alpha<s$ and $\gamma<h\le H$. Its value is $v=\sum b^{\alpha}r^{-\gamma}$, computed modulo $b^{D+s}$.

A **certificate** consists of the following data:
* a *viable set* $W\subseteq\mathbb Z/b^D$;
* a *policy* assigning to each window $z\in\mathbb Z/b^{D+s}$ whose low $D$ digits lie in $W$ a chain $C(z)$
  and a height $h(z)$;
* a potential $V:\mathbb Z/b^D\to\mathbb R$ and a drift bound $g$.

It must satisfy:
1. *(residue)* $z\equiv v(C(z))\pmod P$;
2. *(closure)* $\mathrm{nxt}(z):=r^{h(z)} (z-v(C(z)))/P \bmod b^D$ lies in $W$;
3. *(padding closure)* $x\in W\Rightarrow rx\in W$;
4. *(drift)* for every $x\in W$:
   $\sum_{u\in\mathbb Z/P}\big[h(x+b^Du)+V(\mathrm{nxt}(x+b^Du))\big]\le P (V(x)+g)$.

**Theorem A′.** If a certificate exists with $W\ne\varnothing$ and $g<\lambda$, where $\lambda\ge0$ and
$r^{\lambda}<b^{s}$, then the representable integers have positive lower density.

*Proof outline.* The proof follows the $(7,2)$ note with three changes.
1. The encoding process runs in $\mathbb Z/b^{m}$ with $m=sN+D+s$. Every look-ahead window is then an exact window
   of the residual. We encode residues $y$ whose first $D$ digits form a viable state. By closure, and by padding
   closure on padded steps, the state stays viable at every step. So the policy always has a chain with the right
   residue.
2. The fresh block at step $t$ is the digit block of $y$ at position $st+D$. It is uniform given the past, which we
   prove by averaging over the translations $y\mapsto y+b^{st+D}\delta$. The exponential potential
   $\Psi_t=e^{\theta(G_t-t\lambda+V(X_t))}$ then gives $\mathbb E\Psi_N=O(1)$ uniformly in $N$, and Markov's
   inequality shows that at least half of the viable residues have $G_N\le N\lambda+c_0$.
3. The encoded integers satisfy $n\equiv r^{A}y\pmod{b^{sN}}$ and $n\le C b^{sN}$. So distinct residues mod
   $b^{sN}$ give distinct representable $n$. At least $b^{sN}/(2b^D)$ such $n$ lie below $C b^{sN}$, and positive
   lower density follows.

The full formal proof is `E1110G.pos_lower_density` in `lean/E1110G.lean`. With $W$ equal to all states it
specializes to the $(7,2)$ argument.

## 3. The certificate for (4,3)

Take $b=4$, $r=3$, $s=2$ (blocks of two base-4 digits), $D=14$ (states are 14 base-4 digits, $4^{14}=2^{28}$),
$H=18$, and for each residue class the chains with $h\le\min+12$ (137 chains).
* **Viable set.** Only $11$ of the $16$ residues mod $4^2$ are values of chains. The largest set of states closed
  under every fresh block and under $x\mapsto3x$ has $|W|=178 956 970$, exactly $2/3$ of all states. The stuck
  states number $(4^{12}-1)/3$.
* **Potential.** Value iteration with a 16-digit look-ahead window, 23 iterations (`gvid 4 3 2 14 18 23 12`), gives
  the table `V43_final.bin` (float32, $2^{28}$ entries, SHA-256
  `cc32e163ac5bac97fe5111242e40d7f5ae2bf4f636961b07a6c5cd9ba3f1f080`; xz-compressed 410 MB). Any table that
  passes the checker is a valid certificate, so re-running the search and then the checker also suffices.
* **Exact check** (`verifyd.c`). With $V$ scaled by $2^{20}$ and rounded, the checker rebuilds $W$ from scratch
  (closure under all $16$ fresh blocks and under $\times3$). It verifies that every $x\in W$ and every fresh block has
  a chain leading into $W$ (`bad=0`), and evaluates the drift inequality exactly on all $178 956 970$ viable states:
  $$\max_x\Big(\textstyle\sum_u\min_C[ h 2^{20}+\hat V(\mathrm{nxt}) ]-16 \hat V(x)\Big)=42 192 162,$$
  so $g=42192162/(16\cdot2^{20})=2.5148488\ldots$ It compares with $\lambda=2\cdot29/23=2.5217391\ldots$, and
  $3^{29}<4^{23}$ gives $3^{\lambda}<4^{2}$. **PASS.** The margin is $\lambda-g\approx0.0069$ per block (0.27%).
* **Independent spot check** (`verify43_probe.py`). This program uses Python integers, chains enumerated with
  itertools, $3^{-\gamma}$ via `pow(3,-γ,·)`, and transitions computed on windows with random high digits, which must
  not and do not matter. It recomputes closure and the drift value on randomly sampled viable states.
* The chain and transition code of `verifyd.c` was also validated against the search program at smaller sizes
  (identical $g$).

## 4. Numerical context

These are exact representability tests on random $n$ near $2^L$, using the fact that the smallest-power-of-$q$
summand carries the largest power of $p$. They give the local density of representables:

| $L$ | 32 | 48 | 64 |
|---|---|---|---|
| (4,3) | 0.138 | 0.152 | 0.180 |
| (7,2) | 0.245 | 0.258 | 0.329 |
| (5,2) | 0.975 | 0.9994 | — |
| (9,2) | 0.070 | 0.0605 | 0.0605 |
| (5,3) | 0.052 | 0.043 | 0.040 (0.043 at $L=80$) |

The densities appear to increase toward a limit, and for $(5,2)$ almost all integers are representable. The
certificate method does not reach $(9,2)$ or $(5,3)$ at feasible window sizes: the ratio to the threshold is still
$1.14$–$1.15$. These two pairs remain open.

## Files and reproduction

* `lean/E1110G.lean`: the general theorem `E1110G.pos_lower_density` and the instance `E1110G.erdos1110_43_density`.
  It was checked with Lean `v4.32.0-rc1` and Mathlib `2028213c0d615301c14937e52dcc899ee04481c4` by running
  `lake env lean E1110G.lean` in a Mathlib checkout. It has no `sorry`, and `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]`.
* The table `V43_final.bin.xz` (410 MB) is attached to the GitHub release `v43-certificate` of this repository.
* The checkers are in `certificate/`:
  ```
  xz -dk V43_final.bin.xz
  gcc -O3 -fopenmp -o verifyd verifyd.c -lm
  ./verifyd 4 3 2 14 18 12 V43_final.bin 29 23 W43.bits     # ~10 min on 8 cores; prints GNUM=42192162 ... PASS=1
  python3 verify43_probe.py 4 3 2 14 18 12 V43_final.bin W43.bits 16 20260929   # independent spot check
  ```
* To regenerate the table instead: `gcc -O3 -fopenmp -o gvid gvid.c -lm && ./gvid 4 3 2 14 18 23 12 V.bin`
  (about 1 hour). Any table that passes `verifyd` is a valid certificate.
* `certificate/repdfs.c` is the exact representability test behind the density table in Section 4.
* `certificate/logs/` holds the checker outputs and the per-state cross-check values.
