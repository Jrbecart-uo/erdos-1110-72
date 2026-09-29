# Integers representable by $\lbrace 7,2\rbrace $-antichains have positive lower density

*Jean-Roch Bécart, using Claude Opus 5.5 (Anthropic) via Claude Code. Draft, 2026-09-29.*

*Status: computer-assisted proof. The reduction (certificate ⇒ positive lower density) is formalized in Lean 4 /
Mathlib; the finite certificate is checked by two independently written C programs (not in Lean). The proof, the
programs and the Lean code were produced by the AI under the author's direction; not yet reviewed by a human expert.*

## 1. Statement

Let $p>q\ge 2$ be coprime. Call $n\ge 1$ **representable** if $n=\sum_i p^{a_i}q^{b_i}$ where no summand
divides another. Equivalently, the exponent pairs $(a_i,b_i)$ are distinct and pairwise incomparable in the
product order on $\mathbb N^2$. Erdős and Lewin showed that the non-representable integers form a finite set
iff $\lbrace p,q\rbrace =\lbrace 2,3\rbrace $, and asked about their density (Erdős problem #1110). Yu and Chen showed that the representable
integers have density zero when $q>3$, or $q=3,\ p>6$, or $q=2,\ p>10$. For $(p,q)=(5,2)$, Ding, Li, Liu and Zhang
(proof claim, Aug. 2026) showed positive lower density with a finite certificate modulo $2^{12}$.

**Theorem.** For $(p,q)=(7,2)$ the representable integers have positive lower density:
$\liminf_{x\to\infty} x^{-1}\mathrm{card}\lbrace n\le x:\ n \text{ representable}\rbrace >0.$

The proof has two parts. Theorem A is a general criterion: a finite "potential certificate" implies positive lower
density. Theorem B, checked by computer, says that such a certificate exists for $s=11$.

Throughout, $\mu=\log_7 2$ and $\mathbb Z_2$ denotes the 2-adic integers, in which $7$ is a unit.

## 2. Chains, states, certificates

Fix $s\ge1$ and $P=2^s$. A **chain** is a finite set $C=\lbrace (\alpha_1,\gamma_1),\dots,(\alpha_k,\gamma_k)\rbrace $ with
$0\le\alpha_1<\dots<\alpha_k<s$ and $0\le\gamma_1<\dots<\gamma_k$. Its **height** is $h(C)=\gamma_k+1$ ($h(\varnothing)=0$) and
its **value** is $v(C)=\sum_i 2^{\alpha_i}7^{-\gamma_i}\in\mathbb Z_2$.

A **chain family** of height $\le H$ assigns to each residue $c\in\mathbb Z/P$ a nonempty finite set $\mathcal C(c)$ of
chains with $v(C)\equiv c \pmod P$ and $h(C)\le H$.

The **state space** is $\mathcal X=(\mathbb Z/P)^2$. For $x=(c,b)\in\mathcal X$, a look-ahead $u\in\mathbb Z/P$ and $C\in\mathcal C(c)$,
put $z=c+Pb+P^2u \in \mathbb Z/P^3$ and define $\mathrm{next}(x,u,C)=(c',b')$ by
$$c'+Pb' \equiv 7^{h(C)}\cdot\frac{z-v(C)}{P}\pmod{P^2}.$$
This is well defined because $z\equiv v(C)\pmod P$.

A **certificate** is a chain family together with $V:\mathcal X\to\mathbb R$ and $\hat g\in\mathbb R$ such that for every $x=(c,b)$:
$$\frac1P\sum_{u\in\mathbb Z/P}\ \min_{C\in\mathcal C(c)}\Big[h(C)+V\big(\mathrm{next}(x,u,C)\big)\Big]\ \le\ V(x)+\hat g. \tag{$\ast$}$$

**Theorem A.** If a certificate exists with $\hat g< s\mu$, then the $\lbrace 7,2\rbrace $-representable integers have positive lower
density.

**Theorem B (computation).** Take $s=11$, $H=10$. Let $\mathcal C(c)$ be the set of all chains with $\gamma<10$,
$v\equiv c \pmod{2^{11}}$ and height at most (minimal height for $c$) $+3$. That is 70 701 chains in total, and every residue
is covered. Let $V=\hat V/2^{20}$ with $\hat V$ the integer table below. Then $(\ast)$ holds with
$\hat g = 8385274094/2^{31} = 3.9046975\ldots$, and $\hat g < 11\cdot 26/73 = 3.9178\ldots < 11\mu$ because $7^{26}<2^{73}$.

Theorems A and B together prove the Theorem.

## 3. The encoding

Fix a certificate with $\hat g<s\mu$. Choose $\lambda$ with $\hat g<\lambda<s\mu$ and put $\delta=\lambda-\hat g$. Let
$\pi(x,u)\in\mathcal C(c)$ be a minimiser in $(\ast)$, with ties broken by a fixed rule. Fix an integer $c^\ast\ge0$, to be
chosen later. For $N\ge3$, put $A=\lceil N\lambda\rceil+c^\ast$.

Given $y\in\mathbb Z/2^{sN}$, set $z_0=y$ and $G_0=0$. For $t=0,1,\dots,N-1$ define the following. Here $z_t\in\mathbb Z/2^{s(N-t)}$.

* $c_t=z_t \bmod P$. When $t\le N-2$, $X_t=(c_t,\lfloor z_t/P\rfloor \bmod P)$. When $t\le N-3$, $u_t=\lfloor z_t/P^2\rfloor \bmod P$.
* $C_t=\pi(X_t,u_t)$ if $t\le N-3$. Otherwise $C_t$ is a fixed element of $\mathcal C(c_t)$.
* $G_{t+1}=\max\big(G_t+h(C_t),\ \lceil (t+1)\lambda\rceil\big)$ and $z_{t+1}=7^{G_{t+1}-G_t}\thinspace (z_t-v(C_t))/P$.

Finally set
$$n(y)=\sum_{t<N}\ \sum_{(\alpha,\gamma)\in C_t} 2^{st+\alpha}\thinspace 7^{A-G_t-\gamma}.$$

**Lemma 1.**
(a) The exponent pairs $(st+\alpha,\ A-G_t-\gamma)$ are distinct and pairwise incomparable. If $G_N\le A$, all of them
are $\ge0$, so $n(y)$ is representable (or $0$, which happens only for $y=0$).
(b) If $G_N\le A$, then $n(y)\equiv 7^{A}y \pmod{2^{sN}}$. Hence $y\mapsto n(y)$ is injective on $\lbrace y: G_N(y)\le A\rbrace $.
(c) $n(y)< K\thinspace 2^{sN}$ with $K=2^s7^{c^\ast+1}/(2^s7^{-\lambda}-1)$. Note $2^s 7^{-\lambda}>1$ since $\lambda<s\mu$.

*Proof.* (a) Within block $t$, $\alpha$ and $\gamma$ increase together, so the 2-exponent increases while the
7-exponent decreases. Across blocks $t<t'$, the 2-exponent satisfies $st'+\alpha'\ge s(t+1)>st+\alpha$. The 7-exponent
satisfies $A-G_{t'}-\gamma'\le A-G_{t+1}\le A-G_t-h(C_t)<A-G_t-\gamma$, because $G$ is nondecreasing and $G_{t+1}\ge G_t+h(C_t)$.
Nonnegativity: $A-G_t-\gamma\ge A-G_{t+1}\ge A-G_N$.
(b) By induction on $t$: $y\equiv\sum_{j<t}2^{sj}7^{-G_j}v(C_j)+2^{st}7^{-G_t}z_t \pmod{2^{sN}}$. The step is
$2^{s(t+1)}7^{-G_{t+1}}z_{t+1}=2^{st}7^{-G_t}(z_t-v(C_t))$. At $t=N$ this gives $7^{-A}n(y)\equiv y$.
(c) Since $\sum_{\alpha<s}2^{st+\alpha}<2^{s(t+1)}$ and $G_t\ge\lceil t\lambda\rceil\ge t\lambda$, we get
$n<7^A2^s\sum_{t<N}(2^s7^{-\lambda})^t<7^A 2^s\thinspace \frac{(2^s7^{-\lambda})^N}{2^s7^{-\lambda}-1}$. Finally use $7^{A-N\lambda}\le 7^{c^\ast+1}$. $\square$

## 4. Most $y$ are admissible

Let $y$ be uniform on $\mathbb Z/2^{sN}$. Write $h_t=h(C_t)$ and $E_t=G_t-t\lambda\ge0$. Call step $t$ **padded** if
$G_{t+1}>G_t+h_t$. Then:

1. $E_{t+1}\le\max(E_t+h_t-\lambda,\thinspace 1)\le E_t+H$, using $\lceil a\rceil-a<1$.
2. If step $t\le N-3$ is unpadded, then $E_{t+1}=E_t+h_t-\lambda$ and $X_{t+1}=\mathrm{next}(X_t,u_t,C_t)$. The second claim holds
   because $z_t \bmod P^3=c_t+Pb_t+P^2u_t$.
3. **Fresh look-ahead.** Let $\mathcal F_t=\sigma(y \bmod 2^{s(t+2)})$. The quantities $C_0,\dots,C_{t-1}$, $G_0,\dots,G_t$ and $X_t$ are
   $\mathcal F_t$-measurable, because $C_j$ depends only on $z_j \bmod P^3$, which depends on $y \bmod 2^{s(j+3)}$. Conditionally on
   $\mathcal F_t$, $u_t$ is uniform on $\mathbb Z/P$. Indeed, write $y=y'+2^{s(t+2)}\beta+(\text{higher})$ with $y'=y \bmod 2^{s(t+2)}$ and $\beta$ the
   next block. From the invariant of Lemma 1(b), $u_t=(\text{an }\mathcal F_t\text{-measurable term})+7^{G_t}\beta \bmod P$. Since $7^{G_t}$ is odd,
   this is a bijective image of the uniform, independent block $\beta$.

**Lemma 2.** There is $c_0$, independent of $N$, with $\Pr[E_{N-2}>c_0]\le\tfrac12$.

*Proof.* Normalise $V\ge0$ and let $\mathrm{osc}=\max V$. Put $R=H+\mathrm{osc}+\hat g$, $\theta=\min(1/R,\ \delta/(2R^2))$ and
$\Psi_t=\exp\negthinspace \big(\theta(E_t+V(X_t))\big)$ for $t\le N-2$. Let
$Z_t=h_t+V(\mathrm{next}(X_t,u_t,C_t))-V(X_t)-\hat g$. Then $|Z_t|\le R$. By $(\ast)$, fact 3 and the choice of $\pi$,
$\mathbb E[Z_t\mid\mathcal F_t]\le0$. Facts 1 and 2 give, for $t\le N-3$,
$$\Psi_{t+1}\ \le\ \Psi_t\thinspace e^{-\theta\delta}\thinspace e^{\theta Z_t}\ +\ e^{\theta(1+\mathrm{osc})}.$$
The first term is the unpadded case, where it holds with equality. On a padded step $E_{t+1}<1$, so the second term applies.
Since $e^w\le1+w+w^2$ for $|w|\le1$ and $\theta R\le1$, we have $\mathbb E[e^{\theta Z_t}\mid\mathcal F_t]\le1+\theta^2R^2\le e^{\theta^2R^2}$.
Therefore $\mathbb E\Psi_{t+1}\le\rho\thinspace \mathbb E\Psi_t+e^{\theta(1+\mathrm{osc})}$, where $\rho=e^{-\theta\delta+\theta^2R^2}\le e^{-\theta\delta/2}<1$.
Hence $\mathbb E\Psi_t\le M_0:=e^{\theta\thinspace \mathrm{osc}}+e^{\theta(1+\mathrm{osc})}/(1-\rho)$ for all $t\le N-2$.
Markov's inequality gives $\Pr[E_{N-2}>c_0]\le M_0e^{-\theta c_0}=\tfrac12$ for $c_0=\theta^{-1}\ln(2M_0)$. $\square$

*Proof of Theorem A.* Take $c^\ast=\lceil c_0\rceil+2H$. By fact 1, $E_N\le E_{N-2}+2H$. With probability $\ge\frac12$
this gives $G_N=E_N+N\lambda\le A$. By Lemma 1, at least $2^{sN-1}-1$ distinct representable integers lie below
$K2^{sN}$, for every $N\ge3$. For $K2^{sN}\le x<K2^{s(N+1)}$ we get $\mathrm{card}\lbrace n\le x\rbrace \ge 2^{sN-1}-1\ge x/(2^{s+1}K)-1$. $\square$

The argument is uniform in the pair: it applies verbatim to any $(p,2)$, with $7$ replaced by $p$. After exchanging the roles of the
bases it also applies to any $(p,q)$ with $P=q^s$, provided the chain family covers every residue.

## 5. The certificate (Theorem B)

* **Search.** Exact value iteration on the average-cost MDP $(\ast)$ over $\mathcal X$ ($2^{22}$ states) gives the table.
  The program is `look4.c` (`look4 11 10 14 3`, iteration 8). The table is stored as float32 in `V_s11_it8.bin.xz`, with
  SHA-256 of the uncompressed file `f7f83211…dd9258`. The certificate uses $\hat V=\mathrm{round}(2^{20}V)$, rounding half away from zero.
  All arithmetic in the check is exact integer arithmetic.
* **Check 1** (`verify.c`). This program enumerates chains recursively, computes $7^{-1}$ mod $2^{64}$ by Newton iteration, and
  computes transitions in $\mathbb Z/2^{33}$. It evaluates $(\ast)$ for all $2^{22}$ states: $\max_x$ LHS$-$RHS in units of $2^{-31}$ is
  $8385274094$, attained at state $(c,b)=(1835,623)$. Re-run 2026-09-28 in 3 min 53 s on 8 threads.
* **Check 2** (`verify2.c`, written independently on 2026-09-28). This program enumerates chains as pairs of equal-size
  subsets, computes $7^{-1}=7^{2^{62}-1}$ mod $2^{64}$, and uses full 64-bit 2-adic arithmetic with pseudo-random bits
  above position $3s$, which must not and do not matter. It independently evaluates all $2^{22}$ states and reports the same
  maximum $8385274094$ at the same state. It also checks $7^{26}<2^{73}$ in 128-bit integers. It agrees with Check 1 on 16
  random tables for $s=4,\dots,7$.
* Further cross-checks from the earlier session: a Python big-integer re-implementation matched on 13 states at $s=11$,
  and in full at $s=5,6$. An exhaustive simulation at $s=3$, $N=4$ confirmed exact uniformity of $u_t$ in all conditioning
  classes and injectivity. End-to-end constructions at $s=11$ over up to 900 blocks gave antichains with $n\equiv 7^Ay$ and
  bounded excess.

Margin: $\delta=\lambda-\hat g\approx0.0131$ per 11-bit block, i.e. $0.35497$ vs. $\mu=0.35621$ per bit, about 0.35%.

## 6. Remarks

* **Constants.** For the certificate, $\mathrm{osc}\approx10.28$, $R\approx24.19$ and $\theta\approx1.1\cdot10^{-5}$. This gives
  $c_0\approx1.5\cdot10^6$, so the implied lower density is about $10^{-1.3\cdot10^6}$: positive, but numerically meaningless.
  The observed fraction of representables below $2^{27}$ is $\approx0.22$.
* **Relation to (5,2).** Ding–Li–Liu–Zhang use one block modulo $2^{12}$ with average minimal height $<5<12\log_5 2$.
  For $(7,2)$, the single-block average minimal height exceeds $s\mu$ for every $s\le28$ that we could compute.
  Extrapolating, it needs $s\approx50$. The two-block look-ahead with a potential function is what makes $s=11$ suffice.
* **Other open pairs.** The same method, at sizes we can compute, does not reach $(9,2)$ or $(5,3)$. The exact lower bracket of
  the value iteration, as a ratio to the threshold, is: $(7,2)$: $1.017$ at $s=8$, $1.010$ at $s=9$, $0.9965$ at $s=11$.
  $(9,2)$: $1.145$ at $s=8$, $1.131$ at $s=9$. $(5,3)$ in base 3: $1.155$ at $s=5$, $1.136$ at $s=6$. In base 5 it is worse.
  Extrapolation suggests blocks of about $2^{19}$ or $3^{13}$ would be needed. The heuristic antichain-count exponents
  are $1.127$ for $(7,2)$, $1.045$ for $(9,2)$ and $1.034$ for $(5,3)$, so the margins there really are much thinner.
  $(4,3)$ has congruence obstructions in both orientations.

## Lean formalization (2026-09-29)

`lean/E1110.lean` (1112 lines, Mathlib, `lake env lean` exit 0, no `sorry`/`native_decide`,
axioms `[propext, Classical.choice, Quot.sound]`) proves Theorem A in full:
`E1110.pos_lower_density (K : Cert s H) (lam) (0 ≤ lam) (K.g < lam) ((7:ℝ)^lam < 2^s) :
∃ c > 0, ∃ x₀, ∀ x ≥ x₀, c·x ≤ #{n ≤ x : Representable 7 2 n}`, with `Representable` copied verbatim
from formal-conjectures. `E1110.erdos1110_72_density` specialises to s = 11, H = 10, λ = 286/73 (proving
7^{286/73} < 2^{11} and ĝ < λ in Lean): its only hypothesis is `∃ K : Cert 11 10, K.g = 8385274094/2^31`,
i.e. exactly the finite inequality that `verify.c` / `verify2.c` check. That check (2^22 states × 2^11
look-aheads × ~35 chains) is **trusted to C**, not done in Lean. A toy `Cert 1 1` instance in the file shows the
structure is inhabited (the hypothesis is not vacuous for structural reasons). The Lean proof follows §3–4
with the exponential potential; conditional expectation is replaced by averaging over translations
$y\mapsto y+2^{s(t+2)}\delta$.

## Files and reproduction

* `lean/E1110.lean`: Lean 4 formalization of Theorem A. Checked with Lean `v4.32.0-rc1` and Mathlib commit
  `2028213c0d615301c14937e52dcc899ee04481c4`: `lake env lean E1110.lean` (from a Mathlib checkout).
* `certificate/V_s11_it8.bin.xz`: the potential table (float32, 2^22 entries; SHA-256 of the uncompressed file
  `f7f832116362b96db8ba42884e61803aa5e7cd02071a45f3353072ee4bdd9258`).
* `certificate/verify.c`, `certificate/verify2.c`: the two independent checkers.
  ```
  xz -dk V_s11_it8.bin.xz
  gcc -O3 -fopenmp -o verify verify.c -lm   && ./verify  11 10 3 V_s11_it8.bin 26 73
  gcc -O3 -fopenmp -o verify2 verify2.c -lm && ./verify2 11 10 3 V_s11_it8.bin 26 73
  ```
  Both print `GNUM=8385274094` and `PASS=1` (about 4 minutes each on 8 cores).
* `certificate/look4.c`: value iteration that produced the table (`look4 11 10 14 3`, iteration 8).
  `certificate/gvi.c`: the general-base version used for the (9,2)/(5,3) numbers in §6.
* `certificate/check_rational.py`: 7^26 < 2^73. `review_indep.py`, `indep_probe.py`, `review_fresh_s3.py`, `e2e.py`,
  `simcheck.py`: the smaller cross-checks mentioned in §5.
