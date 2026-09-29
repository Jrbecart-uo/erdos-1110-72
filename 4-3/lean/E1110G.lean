import Mathlib

/-!
# Erdős #1110: positive lower density from a finite look-ahead certificate — general bases

Generalises `E1110.lean` (the `(7,2)` case) to digits in any base `b ≥ 2`, other base `r ≥ 2`
(coprime), blocks of `s` digits, `D`-digit states, and a *viable set* `W` of states (needed when some
residues cannot be the value of any chain, as for `(4,3)`: `n ≢ 2 (mod 3)`, `n ≢ 2 (mod 4)`).

* `E1110G.pos_lower_density`: a certificate `K : Cert b r s D H` with `K.W` nonempty, drift
  `K.g < λ`, `0 ≤ λ` and `r^λ < b^s` implies that the integers that are sums of numbers `r^k b^l`,
  none dividing another (`Representable r b`, copied verbatim from formal-conjectures), have positive
  lower density.
* `E1110G.erdos1110_43_density`: the `(p,q) = (4,3)` instance (`b = 4`, `r = 3`, `s = 2`, `D = 14`,
  `H = 18`, `λ = 58/23`); its only hypothesis is the existence of the certificate that `verifyd.c`
  checks (`g = 42192162 / (16 · 2^20)`). The certificate itself (2^28 states) is not checked in Lean.
* `E1110G.toyCert`: the structure is inhabited.

Proof structure: the process runs in `ZMod (b^m)` with `m = sN + D + s`, so every look-ahead window
is exact; the viable set is invariant (including padded steps, via closure under `x ↦ r x`);
averaging over translations `y ↦ y + b^{st+D} δ` replaces conditional expectation; an exponential
potential gives a Markov bound at time `N`; distinct outputs are counted through the fibres of the
reduction mod `b^{sN}`.
-/

open Finset

namespace E1110G

/-- `Erdos246.Gamma` from formal-conjectures, verbatim. -/
def Gamma (a b : ℕ) : Set ℕ := {x | ∃ k l : ℕ, x = a ^ k * b ^ l}

/-- `Erdos1110.Representable` from formal-conjectures, verbatim. -/
def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Gamma p q ∧ IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n

lemma Gamma_comm (a b : ℕ) : Gamma a b = Gamma b a := by
  ext x; constructor <;> rintro ⟨k, l, rfl⟩ <;> exact ⟨l, k, mul_comm _ _⟩

lemma representable_comm (p q n : ℕ) : Representable p q n ↔ Representable q p n := by
  unfold Representable; rw [Gamma_comm]

/-! ## Digit windows in base `b` -/

section windows
variable {b : ℕ} [NeZero b]

/-- Digits `[k, k+j)` of `w` in base `b`, as an element of `ZMod (b^j)`. -/
def win {m : ℕ} (k j : ℕ) (w : ZMod (b ^ m)) : ZMod (b ^ j) := ((w.val / b ^ k : ℕ) : ZMod (b ^ j))

lemma natCast_mod_pow {m j : ℕ} (h : j ≤ m) (a : ℕ) :
    (((a % b ^ m : ℕ)) : ZMod (b ^ j)) = (a : ZMod (b ^ j)) := by
  rw [ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod_of_dvd a (pow_dvd_pow b h)

lemma nat_win (Y k j m : ℕ) (h : k + j ≤ m) :
    (((Y % b ^ m) / b ^ k : ℕ) : ZMod (b ^ j)) = ((Y / b ^ k : ℕ) : ZMod (b ^ j)) := by
  have hm : b ^ m = b ^ k * b ^ (m - k) := by rw [← pow_add]; congr 1; omega
  rw [hm, Nat.mod_mul_right_div_self]
  exact natCast_mod_pow (by omega) _

/-- The reduction `ZMod (b^m) → ZMod (b^j)`, as a ring hom. -/
abbrev red {m : ℕ} (j : ℕ) (h : j ≤ m) : ZMod (b ^ m) →+* ZMod (b ^ j) :=
  ZMod.castHom (pow_dvd_pow b h) (ZMod (b ^ j))

lemma val_cast_eq_red {m j : ℕ} (h : j ≤ m) (a : ZMod (b ^ m)) :
    ((a.val : ℕ) : ZMod (b ^ j)) = red j h a := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

/-- Core lemma: adding a multiple of `b^k` shifts the window by the multiplier. -/
lemma win_add {m k j : ℕ} (h : k + j ≤ m) (x e : ZMod (b ^ m)) :
    win k j (x + (b : ZMod (b ^ m)) ^ k * e) = win k j x + (e.val : ZMod (b ^ j)) := by
  have hx : x + (b : ZMod (b ^ m)) ^ k * e = ((x.val + b ^ k * e.val : ℕ) : ZMod (b ^ m)) := by
    push_cast; simp only [ZMod.natCast_zmod_val]
  have hb : 0 < b ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne b)) k
  unfold win
  rw [hx, ZMod.val_natCast, nat_win _ _ _ _ h, Nat.add_mul_div_left _ _ hb]
  push_cast
  rfl

lemma win_zero {m k j : ℕ} : win k j (0 : ZMod (b ^ m)) = 0 := by
  simp [win]

lemma win_pow_mul {m k j : ℕ} (h : k + j ≤ m) (e : ZMod (b ^ m)) :
    win k j ((b : ZMod (b ^ m)) ^ k * e) = (e.val : ZMod (b ^ j)) := by
  simpa [win_zero] using win_add h 0 e

lemma natCast_pow_self_eq_zero (j : ℕ) : ((b : ZMod (b ^ j))) ^ j = 0 := by
  have : ((b ^ j : ℕ) : ZMod (b ^ j)) = 0 := ZMod.natCast_self _
  push_cast at this; exact this

/-- Adding a multiple of `b^K` with `K ≥ k + j` does not change the window. -/
lemma win_add_high {m k j K : ℕ} (h : k + j ≤ K) (hK : K ≤ m) (x e : ZMod (b ^ m)) :
    win k j (x + (b : ZMod (b ^ m)) ^ K * e) = win k j x := by
  have hK' : (b : ZMod (b ^ m)) ^ K * e = (b : ZMod (b ^ m)) ^ k * ((b : ZMod (b ^ m)) ^ (K - k) * e) := by
    rw [← mul_assoc, ← pow_add]; congr 2; omega
  rw [hK', win_add (by omega), val_cast_eq_red (by omega)]
  simp only [map_mul, map_pow, map_natCast]
  have hd : ((b : ZMod (b ^ j))) ^ (K - k) = (b : ZMod (b ^ j)) ^ j * (b : ZMod (b ^ j)) ^ (K - k - j) := by
    rw [← pow_add]; congr 1; omega
  rw [hd, natCast_pow_self_eq_zero, zero_mul, zero_mul, add_zero]

lemma win_red {m k j j' : ℕ} (h : j' ≤ j) (x : ZMod (b ^ m)) :
    red j' h (win k j x) = win k j' x := by
  rw [← val_cast_eq_red h, win, ZMod.val_natCast, natCast_mod_pow h]
  rfl

/-- Nested windows: the `D` digits after the first `s` digits of a `(D+s)`-window. -/
lemma win_win {m k s D : ℕ} (h : k + (D + s) ≤ m) (x : ZMod (b ^ m)) :
    win (k + s) D x = ((((win k (D + s) x).val / b ^ s : ℕ)) : ZMod (b ^ D)) := by
  unfold win
  rw [ZMod.val_natCast]
  have h3 : b ^ (D + s) = b ^ s * b ^ D := by rw [← pow_add]; congr 1; omega
  rw [h3, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add]
  exact (natCast_mod_pow le_rfl _).symm

lemma exists_eq_pow_mul {m j : ℕ} (h : j ≤ m) (a : ZMod (b ^ m)) (ha : red j h a = 0) :
    ∃ e, a = (b : ZMod (b ^ m)) ^ j * e := by
  rw [← val_cast_eq_red h, ZMod.natCast_eq_zero_iff] at ha
  obtain ⟨q, hq⟩ := ha
  refine ⟨(q : ZMod (b ^ m)), ?_⟩
  rw [← ZMod.natCast_zmod_val a, hq]
  push_cast; rfl

end windows


/-! ## Inverses, chain values -/

section inverse
variable {b : ℕ} [NeZero b]

/-- `r⁻¹` in `ZMod (b^m)` (a genuine inverse when `r` is coprime to `b`). -/
def invr (b r m : ℕ) : ZMod (b ^ m) := ((r : ZMod (b ^ m)))⁻¹

lemma r_mul_invr {r : ℕ} (hr : Nat.Coprime r b) (m : ℕ) : (r : ZMod (b ^ m)) * invr b r m = 1 :=
  ZMod.coe_mul_inv_eq_one r (Nat.Coprime.pow_right m hr)

lemma rpow_mul_invr_pow {r : ℕ} (hr : Nat.Coprime r b) (m G : ℕ) :
    (r : ZMod (b ^ m)) ^ G * invr b r m ^ G = 1 := by
  rw [← mul_pow, r_mul_invr hr, one_pow]

lemma red_invr {r m j : ℕ} (hr : Nat.Coprime r b) (h : j ≤ m) : red j h (invr b r m) = invr b r j := by
  have h1 := congrArg (red j h) (r_mul_invr hr m)
  rw [map_mul, map_one, map_natCast] at h1
  calc red j h (invr b r m) = (invr b r j * r) * red j h (invr b r m) := by
        rw [mul_comm (invr b r j), r_mul_invr hr, one_mul]
    _ = invr b r j := by rw [mul_assoc, h1, mul_one]

end inverse

/-- Value of a chain `Σ b^α i^γ` (with `i` standing for `r⁻¹`). -/
def cval {R : Type*} [CommRing R] (b : ℕ) (i : R) (C : Finset (ℕ × ℕ)) : R :=
  ∑ a ∈ C, (b : R) ^ a.1 * i ^ a.2

lemma map_cval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (b : ℕ) (i : R) (C : Finset (ℕ × ℕ)) :
    f (cval b i C) = cval b (f i) C := by
  simp [cval, map_sum, map_natCast]

lemma red_cval {b : ℕ} [NeZero b] {r m j : ℕ} (hr : Nat.Coprime r b) (h : j ≤ m) (C : Finset (ℕ × ℕ)) :
    red j h (cval b (invr b r m) C) = cval b (invr b r j) C := by
  rw [map_cval, red_invr hr]

/-! ## Certificates (general bases, `D`-digit states, viable set) -/

/-- Low `D` digits of a `(D+s)`-digit window. -/
abbrev lowD (b s D : ℕ) (z : ZMod (b ^ (D + s))) : ZMod (b ^ D) := ((z.val : ℕ) : ZMod (b ^ D))

/-- Chain value modulo `b^(D+s)`. -/
abbrev vD (b r s D : ℕ) (C : Finset (ℕ × ℕ)) : ZMod (b ^ (D + s)) := cval b (invr b r (D + s)) C

/-- `liftz x u = x + b^D u` as a `(D+s)`-digit window. -/
def liftz (b s D : ℕ) (x : ZMod (b ^ D)) (u : ZMod (b ^ s)) : ZMod (b ^ (D + s)) :=
  ((x.val + b ^ D * u.val : ℕ) : ZMod (b ^ (D + s)))

/-- Next state: `r^h ((z - v(C)) / b^s) mod b^D`. -/
def nxt (b r s D : ℕ) (C : Finset (ℕ × ℕ)) (h : ℕ) (z : ZMod (b ^ (D + s))) : ZMod (b ^ D) :=
  ((r ^ h * ((z - vD b r s D C).val / b ^ s) : ℕ) : ZMod (b ^ D))

/-- A look-ahead potential certificate: digits in base `b`, other base `r`, blocks of `s` digits,
states of `D` digits, heights `≤ H`, a viable set `W` of states, a policy (chain + height for each
`(D+s)`-digit window whose low `D` digits are viable), a potential `V` and a drift bound `g`.
This is what `verifyd.c` checks. -/
structure Cert (b r s D H : ℕ) [NeZero b] where
  W : Finset (ZMod (b ^ D))
  ch : ZMod (b ^ (D + s)) → Finset (ℕ × ℕ)
  hgt : ZMod (b ^ (D + s)) → ℕ
  V : ZMod (b ^ D) → ℝ
  g : ℝ
  chain : ∀ z, ∀ a ∈ ch z, ∀ c ∈ ch z, a.1 < c.1 → a.2 < c.2
  inj : ∀ z, ∀ a ∈ ch z, ∀ c ∈ ch z, a.1 = c.1 → a = c
  alpha_lt : ∀ z, ∀ a ∈ ch z, a.1 < s
  gamma_lt : ∀ z, ∀ a ∈ ch z, a.2 < hgt z
  hgt_le : ∀ z, hgt z ≤ H
  res : ∀ z, lowD b s D z ∈ W → b ^ s ∣ (z - vD b r s D (ch z)).val
  closed : ∀ z, lowD b s D z ∈ W → nxt b r s D (ch z) (hgt z) z ∈ W
  rclosed : ∀ x ∈ W, (r : ZMod (b ^ D)) * x ∈ W
  drift : ∀ x ∈ W,
    ∑ u : ZMod (b ^ s), ((hgt (liftz b s D x u) : ℝ) +
      V (nxt b r s D (ch (liftz b s D x u)) (hgt (liftz b s D x u)) (liftz b s D x u)))
      ≤ b ^ s * (V x + g)

lemma Cert.rpow_closed {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (k : ℕ) :
    ∀ x ∈ K.W, (r : ZMod (b ^ D)) ^ k * x ∈ K.W := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; rw [pow_succ', mul_assoc]; exact K.rclosed _ (ih x hx)

/-! ## The encoding process -/

noncomputable section process
variable {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam : ℝ) {m : ℕ}

/-- The `(D+s)`-digit window read at step `t`. -/
def zAt (b r s D : ℕ) (t G : ℕ) (ρ : ZMod (b ^ m)) : ZMod (b ^ (D + s)) :=
  win (s * t) (D + s) ((r : ZMod (b ^ m)) ^ G * ρ)

def step (t : ℕ) (p : ℕ × ZMod (b ^ m)) : ℕ × ZMod (b ^ m) :=
  (max (p.1 + K.hgt (zAt b r s D t p.1 p.2)) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊,
   p.2 - (b : ZMod (b ^ m)) ^ (s * t) * invr b r m ^ p.1 * cval b (invr b r m) (K.ch (zAt b r s D t p.1 p.2)))

def proc (y : ZMod (b ^ m)) : ℕ → ℕ × ZMod (b ^ m)
  | 0 => (0, y)
  | t + 1 => step K lam t (proc y t)

variable (y : ZMod (b ^ m))

abbrev GG (t : ℕ) : ℕ := (proc K lam y t).1
abbrev RR (t : ℕ) : ZMod (b ^ m) := (proc K lam y t).2
abbrev WW (t : ℕ) : ZMod (b ^ m) := (r : ZMod (b ^ m)) ^ GG K lam y t * RR K lam y t
abbrev ZZ (t : ℕ) : ZMod (b ^ (D + s)) := win (s * t) (D + s) (WW K lam y t)
/-- The state (`D`-digit window) at step `t`. -/
abbrev XX (t : ℕ) : ZMod (b ^ D) := win (s * t) D (WW K lam y t)
abbrev CC (t : ℕ) : Finset (ℕ × ℕ) := K.ch (ZZ K lam y t)
abbrev hh (t : ℕ) : ℕ := K.hgt (ZZ K lam y t)

lemma GG_succ (t : ℕ) : GG K lam y (t + 1) = max (GG K lam y t + hh K lam y t) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ := rfl

lemma RR_succ (t : ℕ) : RR K lam y (t + 1) =
    RR K lam y t - (b : ZMod (b ^ m)) ^ (s * t) * invr b r m ^ GG K lam y t * cval b (invr b r m) (CC K lam y t) := rfl

lemma GG_zero : GG K lam y 0 = 0 := rfl

lemma GG_le_succ (t : ℕ) : GG K lam y t + hh K lam y t ≤ GG K lam y (t + 1) := by
  rw [GG_succ]; exact le_max_left _ _

lemma GG_mono {t t' : ℕ} (h : t ≤ t') : GG K lam y t ≤ GG K lam y t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_trans (Nat.le_add_right _ _) (GG_le_succ K lam y _))

lemma ceil_le_GG (t : ℕ) : ⌈(t : ℝ) * lam⌉₊ ≤ GG K lam y t := by
  cases t with
  | zero => simp
  | succ t => rw [GG_succ]; exact le_max_right _ _

/-- Telescoping: `y = Σ_{j<t} b^{sj} r^{-G_j} v(C_j) + ρ_t`. -/
lemma y_eq_sum (t : ℕ) : y = (∑ j ∈ range t, (b : ZMod (b ^ m)) ^ (s * j) * invr b r m ^ GG K lam y j *
    cval b (invr b r m) (CC K lam y j)) + RR K lam y t := by
  induction t with
  | zero => simp [RR, proc]
  | succ t ih => rw [sum_range_succ, RR_succ]; linear_combination ih

lemma lowD_ZZ (t : ℕ) : lowD b s D (ZZ K lam y t) = XX K lam y t := by
  show ((win (s * t) (D + s) (WW K lam y t)).val : ZMod (b ^ D)) = win (s * t) D (WW K lam y t)
  rw [win, ZMod.val_natCast, natCast_mod_pow (by omega)]; rfl

/-- One step of the invariant: divisibility of `ρ` and viability of the state propagate, and the
next state is `r^pad · nxt(window)` (padded steps multiply by `r^pad`). -/
lemma inv_step {N : ℕ} (hr : Nat.Coprime r b) (hm : s * N + (D + s) ≤ m) (t : ℕ) (ht : t < N)
    (hdiv : ∃ q, RR K lam y t = (b : ZMod (b ^ m)) ^ (s * t) * q) (hW : XX K lam y t ∈ K.W) :
    (∃ q, RR K lam y (t + 1) = (b : ZMod (b ^ m)) ^ (s * (t + 1)) * q) ∧
    XX K lam y (t + 1) = (r : ZMod (b ^ D)) ^ (GG K lam y (t + 1) - GG K lam y t - hh K lam y t) *
      nxt b r s D (CC K lam y t) (hh K lam y t) (ZZ K lam y t) := by
  obtain ⟨q, hq⟩ := hdiv
  have hstm : s * t + (D + s) ≤ m := by
    have := Nat.mul_le_mul_left s (show t + 1 ≤ N by omega); rw [mul_add, mul_one] at this; omega
  have hs_m : s ≤ m := by omega
  set G := GG K lam y t
  set C := CC K lam y t
  set h := hh K lam y t
  have hWz : lowD b s D (ZZ K lam y t) ∈ K.W := by rw [lowD_ZZ]; exact hW
  -- residue condition: r^G q ≡ v(C) mod b^s
  have hres := K.res _ hWz
  rw [← ZMod.natCast_eq_zero_iff, val_cast_eq_red (m := D + s) (j := s) (by omega), map_sub] at hres
  have hv : red s (by omega : s ≤ D + s) (vD b r s D C) = cval b (invr b r s) C := red_cval hr _ _
  have hz : red s (by omega : s ≤ D + s) (ZZ K lam y t) = red s hs_m ((r : ZMod (b ^ m)) ^ G * q) := by
    show red s _ (win (s * t) (D + s) _) = _
    rw [win_red (by omega)]
    show win (s * t) s ((r : ZMod (b ^ m)) ^ G * RR K lam y t) = _
    rw [hq, mul_left_comm, win_pow_mul (by omega), val_cast_eq_red (by omega)]
  rw [hz, hv] at hres
  have h0 : red s hs_m ((r : ZMod (b ^ m)) ^ G * q - cval b (invr b r m) C) = 0 := by
    rw [map_sub, red_cval hr]; exact hres
  obtain ⟨e, he⟩ := exists_eq_pow_mul _ _ h0
  have hRR : RR K lam y (t + 1) = (b : ZMod (b ^ m)) ^ (s * (t + 1)) * (invr b r m ^ G * e) := by
    rw [RR_succ, hq]
    have : q - invr b r m ^ G * cval b (invr b r m) C = invr b r m ^ G * ((r : ZMod (b ^ m)) ^ G * q - cval b (invr b r m) C) := by
      linear_combination (-q) * rpow_mul_invr_pow hr m G
    rw [mul_add s t 1, mul_one, pow_add, show (b : ZMod (b ^ m)) ^ (s * t) * q - (b : ZMod (b ^ m)) ^ (s * t) * invr b r m ^ G *
      cval b (invr b r m) C = (b : ZMod (b ^ m)) ^ (s * t) * (q - invr b r m ^ G * cval b (invr b r m) C) by ring, this, he]
    ring
  refine ⟨⟨_, hRR⟩, ?_⟩
  -- the window identity  WW t - b^{st} v = b^{st} (b^s (r^G r'))  with r' = invr^G e
  set r' := invr b r m ^ G * e
  have hw : WW K lam y t + (b : ZMod (b ^ m)) ^ (s * t) * (-cval b (invr b r m) C) =
      (b : ZMod (b ^ m)) ^ (s * t) * ((b : ZMod (b ^ m)) ^ s * ((r : ZMod (b ^ m)) ^ G * r')) := by
    have e1 := RR_succ K lam y t
    rw [hRR] at e1
    show (r : ZMod (b ^ m)) ^ G * RR K lam y t + _ = _
    linear_combination (-(r : ZMod (b ^ m)) ^ G) * e1 +
      ((b : ZMod (b ^ m)) ^ (s * t) * cval b (invr b r m) C) * rpow_mul_invr_pow hr m G
  have hDs : D + s ≤ m := by omega
  have hsD : s * (t + 1) + D ≤ m := by
    have := Nat.mul_le_mul_left s (show t + 1 ≤ N by omega); omega
  -- the window after subtracting the chain
  have hzv : ZZ K lam y t - vD b r s D C =
      (b : ZMod (b ^ (D + s))) ^ s * ((r : ZMod (b ^ (D + s))) ^ G * red (D + s) hDs r') := by
    have h1 := win_add (k := s * t) (j := D + s) hstm (WW K lam y t) (-cval b (invr b r m) C)
    rw [hw, win_pow_mul hstm, val_cast_eq_red hDs, val_cast_eq_red hDs] at h1
    simp only [map_mul, map_pow, map_natCast, map_neg, red_cval hr] at h1
    show ZZ K lam y t - cval b (invr b r (D + s)) C = _
    linear_combination -h1
  have hred : ∀ x : ZMod (b ^ m), red D (by omega : D ≤ D + s) (red (D + s) hDs x) = red D (by omega : D ≤ m) x := by
    intro x
    rw [← val_cast_eq_red (m := D + s) (j := D) (by omega), ← val_cast_eq_red hDs, ZMod.val_natCast,
      natCast_mod_pow (by omega), val_cast_eq_red]
  have hnxt : nxt b r s D C h (ZZ K lam y t) =
      (r : ZMod (b ^ D)) ^ h * ((r : ZMod (b ^ D)) ^ G * red D (by omega : D ≤ m) r') := by
    have e : nxt b r s D C h (ZZ K lam y t) = (r : ZMod (b ^ D)) ^ h * win s D (ZZ K lam y t - vD b r s D C) := by
      unfold nxt win; push_cast; rfl
    rw [e, hzv, win_pow_mul (m := D + s) (k := s) (j := D) (by omega), val_cast_eq_red (by omega : D ≤ D + s)]
    simp only [map_mul, map_pow, map_natCast]
    rw [hred]
  have hXX : XX K lam y (t + 1) = (r : ZMod (b ^ D)) ^ GG K lam y (t + 1) * red D (by omega : D ≤ m) r' := by
    show win (s * (t + 1)) D ((r : ZMod (b ^ m)) ^ GG K lam y (t + 1) * RR K lam y (t + 1)) = _
    rw [hRR, mul_left_comm, win_pow_mul hsD, val_cast_eq_red (by omega : D ≤ m)]
    simp only [map_mul, map_pow, map_natCast]
  have hG' : GG K lam y (t + 1) = (GG K lam y (t + 1) - G - h) + h + G := by
    have := GG_le_succ K lam y t; omega
  rw [hXX, hnxt, hG', pow_add, pow_add]
  have : GG K lam y (t + 1) - G - h = (GG K lam y (t + 1) - G - h) + h + G - G - h := by omega
  rw [← this]; ring

/-- The invariant along the whole run: `ρ_t` divisible by `b^{st}` and the state viable. -/
lemma invariant {N : ℕ} (hr : Nat.Coprime r b) (hm : s * N + (D + s) ≤ m) (hy : XX K lam y 0 ∈ K.W) :
    ∀ t ≤ N, (∃ q, RR K lam y t = (b : ZMod (b ^ m)) ^ (s * t) * q) ∧ XX K lam y t ∈ K.W := by
  intro t ht
  induction t with
  | zero => exact ⟨⟨y, by simp [RR, proc]⟩, hy⟩
  | succ t ih =>
    obtain ⟨hd, hW⟩ := ih (by omega)
    obtain ⟨hd', hX⟩ := inv_step K lam y hr hm t (by omega) hd hW
    refine ⟨hd', ?_⟩
    rw [hX]
    apply K.rpow_closed
    apply K.closed
    rw [lowD_ZZ]; exact hW

end process


/-! ## The integer `n(y)`: congruence, injectivity, representability -/

lemma pow_pow_dvd {b r a c a' c' : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) (hbr : Nat.Coprime b r)
    (h : b ^ a * r ^ c ∣ b ^ a' * r ^ c') : a ≤ a' ∧ c ≤ c' := by
  constructor
  · have h1 : b ^ a ∣ b ^ a' * r ^ c' := dvd_trans (dvd_mul_right _ _) h
    have hc : Nat.Coprime (b ^ a) (r ^ c') := Nat.Coprime.pow _ _ hbr
    exact (Nat.pow_dvd_pow_iff_le_right (by omega)).mp (hc.dvd_of_dvd_mul_right h1)
  · have h1 : r ^ c ∣ b ^ a' * r ^ c' := dvd_trans (dvd_mul_left _ _) h
    have hc : Nat.Coprime (r ^ c) (b ^ a') := Nat.Coprime.pow _ _ hbr.symm
    exact (Nat.pow_dvd_pow_iff_le_right (by omega)).mp (hc.dvd_of_dvd_mul_left h1)

lemma rpow_sub {b : ℕ} [NeZero b] {r m A k : ℕ} (hr : Nat.Coprime r b) (h : k ≤ A) :
    (r : ZMod (b ^ m)) ^ (A - k) = (r : ZMod (b ^ m)) ^ A * invr b r m ^ k := by
  have : (r : ZMod (b ^ m)) ^ A = (r : ZMod (b ^ m)) ^ (A - k) * (r : ZMod (b ^ m)) ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc, rpow_mul_invr_pow hr, mul_one]

noncomputable section encoding
variable {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam : ℝ) {m : ℕ} (y : ZMod (b ^ m))

/-- The index set of summands. -/
def idx (N : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) := (range N).sigma (fun t => CC K lam y t)

/-- Exponent pair of a summand: (`b`-exponent, `r`-exponent). -/
def ex1 (s : ℕ) (i : Σ _ : ℕ, ℕ × ℕ) : ℕ := s * i.1 + i.2.1
def ex2 (A : ℕ) (i : Σ _ : ℕ, ℕ × ℕ) : ℕ := A - GG K lam y i.1 - i.2.2

/-- The encoded integer `n(y) = Σ b^{st+α} r^{A-G_t-γ}`. -/
def nval (A N : ℕ) : ℕ := ∑ i ∈ idx K lam y N, b ^ ex1 s i * r ^ ex2 K lam y A i

lemma gamma_add_lt {N A t : ℕ} (hA : GG K lam y N ≤ A) (ht : t < N) {a : ℕ × ℕ} (ha : a ∈ CC K lam y t) :
    GG K lam y t + a.2 < GG K lam y (t + 1) ∧ GG K lam y (t + 1) ≤ A :=
  ⟨lt_of_lt_of_le (Nat.add_lt_add_left (K.gamma_lt _ a ha) _) (GG_le_succ K lam y t),
   le_trans (GG_mono K lam y (by omega)) hA⟩

lemma anti {N A : ℕ} (hA : GG K lam y N ≤ A) {i j : Σ _ : ℕ, ℕ × ℕ}
    (hi : i ∈ idx K lam y N) (hj : j ∈ idx K lam y N) (hlt : i.1 < j.1 ∨ (i.1 = j.1 ∧ i.2.1 < j.2.1)) :
    ex1 s i < ex1 s j ∧ ex2 K lam y A j < ex2 K lam y A i := by
  simp only [idx, mem_sigma, mem_range] at hi hj
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  have ai := gamma_add_lt K lam y hA hi1 hi2
  have aj := gamma_add_lt K lam y hA hj1 hj2
  have hαi := K.alpha_lt _ _ hi2
  unfold ex1 ex2
  rcases hlt with h | ⟨h1, h2⟩
  · have hmono := GG_mono K lam y (show i.1 + 1 ≤ j.1 by omega)
    constructor
    · have : s * (i.1 + 1) ≤ s * j.1 := Nat.mul_le_mul_left _ (by omega)
      rw [mul_add, mul_one] at this; omega
    · omega
  · obtain ⟨ti, ai'⟩ := i
    obtain ⟨tj, aj'⟩ := j
    simp only at h1 h2 hi2 hj2 ai aj ⊢
    subst h1
    have := K.chain _ ai' hi2 aj' hj2 h2
    omega

lemma ne_lt {i j : Σ _ : ℕ, ℕ × ℕ} {N : ℕ} (hi : i ∈ idx K lam y N) (hj : j ∈ idx K lam y N) (hne : i ≠ j) :
    (i.1 < j.1 ∨ (i.1 = j.1 ∧ i.2.1 < j.2.1)) ∨ (j.1 < i.1 ∨ (j.1 = i.1 ∧ j.2.1 < i.2.1)) := by
  obtain ⟨ti, ai⟩ := i
  obtain ⟨tj, aj⟩ := j
  simp only
  rcases lt_trichotomy ti tj with h | h | h
  · exact Or.inl (Or.inl h)
  · subst h
    simp only [idx, mem_sigma, mem_range] at hi hj
    rcases lt_trichotomy ai.1 aj.1 with h' | h' | h'
    · exact Or.inl (Or.inr ⟨rfl, h'⟩)
    · exact absurd (by rw [K.inj _ ai hi.2 aj hj.2 h']) hne
    · exact Or.inr (Or.inr ⟨rfl, h'⟩)
  · exact Or.inr (Or.inl h)

lemma nval_representable (hb : 2 ≤ b) (hr2 : 2 ≤ r) (hbr : Nat.Coprime b r) {N A : ℕ}
    (hA : GG K lam y N ≤ A) : Representable r b (nval K lam y A N) := by
  set f : (Σ _ : ℕ, ℕ × ℕ) → ℕ := fun i => b ^ ex1 s i * r ^ ex2 K lam y A i with hf
  have key : ∀ i ∈ idx K lam y N, ∀ j ∈ idx K lam y N, i ≠ j → ¬ f i ∣ f j := by
    intro i hi j hj hne hdvd
    have hd := pow_pow_dvd hb hr2 hbr hdvd
    rcases ne_lt K lam y hi hj hne with h | h
    · have := anti K lam y hA hi hj h; omega
    · have := anti K lam y hA hj hi h; omega
  have hinj : Set.InjOn f (idx K lam y N) := by
    intro i hi j hj hij
    by_contra hne
    exact key i hi j hj hne (hij ▸ dvd_refl _)
  refine ⟨(idx K lam y N).image f, ?_, ?_, ?_⟩
  · intro x hx
    simp only [coe_image, Set.mem_image, mem_coe] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨ex2 K lam y A i, ex1 s i, by rw [hf, mul_comm]⟩
  · intro x hx x' hx' hne
    simp only [coe_image, Set.mem_image, mem_coe] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hx'
    exact key i hi j hj (fun h => hne (h ▸ rfl))
  · rw [sum_image (fun i hi j hj h => hinj hi hj h)]
    rfl

/-- `n(y) ≡ r^A (y - ρ_N)` exactly in `ZMod (b^m)`, for admissible `y`. -/
lemma nval_cast (hr : Nat.Coprime r b) {N A : ℕ} (hA : GG K lam y N ≤ A) :
    ((nval K lam y A N : ℕ) : ZMod (b ^ m)) = (r : ZMod (b ^ m)) ^ A * (y - RR K lam y N) := by
  have hy := y_eq_sum K lam y N
  have hy' : y - RR K lam y N = ∑ j ∈ range N, (b : ZMod (b ^ m)) ^ (s * j) * invr b r m ^ GG K lam y j *
      cval b (invr b r m) (CC K lam y j) := by linear_combination hy
  rw [hy', nval, idx, sum_sigma, Nat.cast_sum, mul_sum]
  refine sum_congr rfl (fun t ht => ?_)
  rw [Nat.cast_sum, cval, mul_sum, mul_sum]
  refine sum_congr rfl (fun a ha => ?_)
  have hle := gamma_add_lt K lam y hA (mem_range.mp ht) ha
  unfold ex1 ex2
  push_cast
  rw [Nat.sub_sub, rpow_sub hr (by omega), pow_add, pow_add]
  ring

/-- Modulo `b^{sN}`, `n(y) ≡ r^A y`; hence `y ↦ n(y)` is injective modulo `b^{sN}`. -/
lemma nval_red (hr : Nat.Coprime r b) {N A : ℕ} (hm : s * N + (D + s) ≤ m) (hy : XX K lam y 0 ∈ K.W)
    (hA : GG K lam y N ≤ A) :
    red (s * N) (by omega) ((nval K lam y A N : ℕ) : ZMod (b ^ m)) =
      (r : ZMod (b ^ (s * N))) ^ A * red (s * N) (by omega) y := by
  obtain ⟨⟨q, hq⟩, _⟩ := invariant K lam y hr hm hy N le_rfl
  rw [nval_cast K lam y hr hA, hq]
  simp only [map_mul, map_pow, map_natCast, map_sub]
  rw [natCast_pow_self_eq_zero, zero_mul, sub_zero]

lemma nval_inj (hr : Nat.Coprime r b) {N A : ℕ} (hm : s * N + (D + s) ≤ m) {y y' : ZMod (b ^ m)}
    (hy : XX K lam y 0 ∈ K.W) (hy' : XX K lam y' 0 ∈ K.W)
    (hA : GG K lam y N ≤ A) (hA' : GG K lam y' N ≤ A) (h : nval K lam y A N = nval K lam y' A N) :
    red (s * N) (by omega) y = red (s * N) (by omega) y' := by
  have h1 := nval_red K lam y hr hm hy hA
  have h2 := nval_red K lam y' hr hm hy' hA'
  rw [h, h2] at h1
  calc red (s * N) _ y = ((r : ZMod (b ^ (s * N))) ^ A * invr b r (s * N) ^ A) * red (s * N) _ y := by
        rw [rpow_mul_invr_pow hr, one_mul]
    _ = invr b r (s * N) ^ A * ((r : ZMod (b ^ (s * N))) ^ A * red (s * N) _ y) := by ring
    _ = invr b r (s * N) ^ A * ((r : ZMod (b ^ (s * N))) ^ A * red (s * N) _ y') := by rw [h1]
    _ = ((r : ZMod (b ^ (s * N))) ^ A * invr b r (s * N) ^ A) * red (s * N) _ y' := by ring
    _ = red (s * N) _ y' := by rw [rpow_mul_invr_pow hr, one_mul]

end encoding


/-! ## Size bound -/

lemma geom_lt {b : ℕ} (hb : 2 ≤ b) (s : ℕ) : ∑ x ∈ range s, b ^ x < b ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ, pow_succ]
    have : b ^ s + b ^ s ≤ b ^ s * b := by nlinarith [pow_pos (show 0 < b by omega) s]
    omega

lemma sum_fst_lt {b r s D H : ℕ} [NeZero b] (hb : 2 ≤ b) (K : Cert b r s D H) (z : ZMod (b ^ (D + s))) :
    ∑ a ∈ K.ch z, b ^ a.1 < b ^ s := by
  have hinj : Set.InjOn Prod.fst (K.ch z : Set (ℕ × ℕ)) := fun a ha c hc h => K.inj z a ha c hc h
  rw [← sum_image (f := fun x => b ^ x) (fun a ha c hc h => hinj ha hc h)]
  refine lt_of_le_of_lt (sum_le_sum_of_subset (fun x hx => ?_)) (geom_lt hb s)
  simp only [mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact mem_range.mpr (K.alpha_lt z a ha)

lemma geom_aux (ℓ q : ℝ) (hℓ : 0 ≤ ℓ) (hq : ℓ < q) (N : ℕ) :
    ∑ t ∈ range N, q ^ t * ℓ ^ (N - t) ≤ q ^ N * ℓ / (q - ℓ) := by
  have hpos : 0 < q - ℓ := sub_pos.mpr hq
  induction N with
  | zero => simp only [range_zero, sum_empty, pow_zero, one_mul]; exact div_nonneg hℓ hpos.le
  | succ N ih =>
    rw [sum_range_succ, show N + 1 - N = 1 by omega, pow_one]
    have hs : ∑ t ∈ range N, q ^ t * ℓ ^ (N + 1 - t) = ℓ * ∑ t ∈ range N, q ^ t * ℓ ^ (N - t) := by
      rw [mul_sum]
      refine sum_congr rfl (fun t ht => ?_)
      rw [show N + 1 - t = (N - t) + 1 by have := mem_range.mp ht; omega, pow_succ]
      ring
    rw [hs, le_div_iff₀ hpos]
    rw [le_div_iff₀ hpos] at ih
    have := mul_le_mul_of_nonneg_left ih hℓ
    have hq0 : 0 ≤ q := hℓ.trans hq.le
    rw [pow_succ]
    nlinarith [pow_nonneg hq0 N]

noncomputable section sizes
variable {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam : ℝ) {m : ℕ} (y : ZMod (b ^ m))

lemma nval_le_nat (hb : 2 ≤ b) (hr0 : 0 < r) (A N : ℕ) :
    nval K lam y A N ≤ ∑ t ∈ range N, b ^ s * b ^ (s * t) * r ^ (A - GG K lam y t) := by
  rw [nval, idx, sum_sigma]
  refine sum_le_sum (fun t _ => ?_)
  calc ∑ a ∈ CC K lam y t, b ^ ex1 s ⟨t, a⟩ * r ^ ex2 K lam y A ⟨t, a⟩
      ≤ ∑ a ∈ CC K lam y t, b ^ (s * t) * r ^ (A - GG K lam y t) * b ^ a.1 := by
        refine sum_le_sum (fun a _ => ?_)
        unfold ex1 ex2
        rw [pow_add]
        have : r ^ (A - GG K lam y t - a.2) ≤ r ^ (A - GG K lam y t) :=
          Nat.pow_le_pow_right hr0 (Nat.sub_le _ _)
        calc b ^ (s * t) * b ^ a.1 * r ^ (A - GG K lam y t - a.2)
            ≤ b ^ (s * t) * b ^ a.1 * r ^ (A - GG K lam y t) := Nat.mul_le_mul_left _ this
          _ = _ := by ring
    _ = b ^ (s * t) * r ^ (A - GG K lam y t) * ∑ a ∈ CC K lam y t, b ^ a.1 := by rw [mul_sum]
    _ ≤ b ^ (s * t) * r ^ (A - GG K lam y t) * b ^ s := Nat.mul_le_mul_left _ (sum_fst_lt hb K _).le
    _ = _ := by ring

lemma rpow_GG_ge (hr1 : (1 : ℝ) ≤ r) (t : ℕ) : ((r : ℝ) ^ lam) ^ t ≤ (r : ℝ) ^ GG K lam y t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hr1
  have := ceil_le_GG K lam y t
  have h2 := Nat.le_ceil ((t : ℝ) * lam)
  have h3 : ((⌈(t : ℝ) * lam⌉₊ : ℕ) : ℝ) ≤ (GG K lam y t : ℝ) := by exact_mod_cast this
  linarith

/-- `n(y) ≤ b^s r^Dc (b^s)^N ℓ / (b^s - ℓ)` with `ℓ = r^λ`, for admissible `y`. -/
lemma nval_le_real (hb : 2 ≤ b) (hr2 : 2 ≤ r) {N A : ℕ} (hA : GG K lam y N ≤ A)
    (hlam : (r : ℝ) ^ lam < (b : ℝ) ^ s) (Dc : ℝ) (hAD : (A : ℝ) ≤ N * lam + Dc) :
    (nval K lam y A N : ℝ) ≤ (b : ℝ) ^ s * (r : ℝ) ^ Dc * (((b : ℝ) ^ s) ^ N * (r : ℝ) ^ lam / ((b : ℝ) ^ s - (r : ℝ) ^ lam)) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hr0 : (0 : ℝ) < r := by linarith
  set ℓ : ℝ := (r : ℝ) ^ lam with hℓ
  have hℓ0 : 0 < ℓ := Real.rpow_pos_of_pos hr0 _
  have hrA : (r : ℝ) ^ A ≤ (r : ℝ) ^ Dc * ℓ ^ N := by
    rw [← Real.rpow_natCast, hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
    apply Real.rpow_le_rpow_of_exponent_le hr1
    linarith
  have hterm : ∀ t ∈ range N, (r : ℝ) ^ (A - GG K lam y t) ≤ (r : ℝ) ^ Dc * ℓ ^ (N - t) := by
    intro t ht
    have htN := mem_range.mp ht
    have hGA : GG K lam y t ≤ A := le_trans (GG_mono K lam y htN.le) hA
    have hrG : (0 : ℝ) < (r : ℝ) ^ GG K lam y t := by positivity
    refine le_of_mul_le_mul_right ?_ hrG
    rw [← pow_add, Nat.sub_add_cancel hGA]
    calc (r : ℝ) ^ A ≤ (r : ℝ) ^ Dc * ℓ ^ N := hrA
      _ = (r : ℝ) ^ Dc * ℓ ^ (N - t) * ℓ ^ t := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel htN.le]
      _ ≤ (r : ℝ) ^ Dc * ℓ ^ (N - t) * (r : ℝ) ^ GG K lam y t := by
          gcongr
          exact rpow_GG_ge K lam y hr1 t
  have h1 : (nval K lam y A N : ℝ) ≤ ∑ t ∈ range N, (b : ℝ) ^ s * (b : ℝ) ^ (s * t) * (r : ℝ) ^ (A - GG K lam y t) := by
    exact_mod_cast nval_le_nat K lam y hb (by omega) A N
  refine h1.trans ?_
  have hlam' : ℓ < (b : ℝ) ^ s := hlam
  calc ∑ t ∈ range N, (b : ℝ) ^ s * (b : ℝ) ^ (s * t) * (r : ℝ) ^ (A - GG K lam y t)
      ≤ ∑ t ∈ range N, (b : ℝ) ^ s * (r : ℝ) ^ Dc * (((b : ℝ) ^ s) ^ t * ℓ ^ (N - t)) := by
        refine sum_le_sum (fun t ht => ?_)
        rw [pow_mul]
        have := hterm t ht
        have : (0 : ℝ) ≤ (b : ℝ) ^ s * ((b : ℝ) ^ s) ^ t := by positivity
        nlinarith
    _ = (b : ℝ) ^ s * (r : ℝ) ^ Dc * ∑ t ∈ range N, ((b : ℝ) ^ s) ^ t * ℓ ^ (N - t) := by rw [mul_sum]
    _ ≤ _ := by
        gcongr
        exact geom_aux ℓ ((b : ℝ) ^ s) hℓ0.le hlam' N

end sizes


/-! ## Fresh look-ahead: locality, fibers, averaging -/

lemma lift_eq {b : ℕ} [NeZero b] (s D : ℕ) (z : ZMod (b ^ (D + s))) (E : ℕ) :
    z + (b : ZMod (b ^ (D + s))) ^ D * (E : ZMod (b ^ (D + s))) =
      liftz b s D (z.val : ZMod (b ^ D)) (((z.val / b ^ D + E : ℕ) : ZMod (b ^ s))) := by
  have hL : ((z.val + b ^ D * E : ℕ) : ZMod (b ^ (D + s))) = z + (b : ZMod (b ^ (D + s))) ^ D * (E : ZMod (b ^ (D + s))) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [← hL, liftz, ZMod.val_natCast, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff']
  set a := z.val
  set q := a / b ^ D + E
  have h1 : a + b ^ D * E = (a % b ^ D + b ^ D * (q % b ^ s)) + b ^ (D + s) * (q / b ^ s) := by
    calc a + b ^ D * E = a % b ^ D + b ^ D * (a / b ^ D) + b ^ D * E := by rw [Nat.mod_add_div]
      _ = a % b ^ D + b ^ D * q := by ring
      _ = a % b ^ D + b ^ D * (q % b ^ s + b ^ s * (q / b ^ s)) := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [h1, Nat.add_mul_mod_self_left]

lemma fiber {b : ℕ} [NeZero b] (s D : ℕ) (F : ZMod (b ^ (D + s)) → ℝ) (z : ZMod (b ^ (D + s)))
    (c : ZMod (b ^ s)) (hc : IsUnit c) (e : ZMod (b ^ s) → ℕ) (he : ∀ δ, ((e δ : ℕ) : ZMod (b ^ s)) = c * δ) :
    ∑ δ : ZMod (b ^ s), F (z + (b : ZMod (b ^ (D + s))) ^ D * (e δ : ZMod (b ^ (D + s)))) =
      ∑ u : ZMod (b ^ s), F (liftz b s D (z.val : ZMod (b ^ D)) u) := by
  refine Fintype.sum_equiv ((Units.mulLeft hc.unit).trans (Equiv.addLeft ((z.val / b ^ D : ℕ) : ZMod (b ^ s))))
    _ _ (fun δ => ?_)
  rw [lift_eq]
  congr 2
  push_cast
  rw [he]
  rfl

lemma isUnit_rpow {b : ℕ} [NeZero b] {r : ℕ} (hr : Nat.Coprime r b) (s G : ℕ) : IsUnit ((r : ZMod (b ^ s)) ^ G) :=
  (IsUnit.of_mul_eq_one _ (r_mul_invr hr s)).pow G

noncomputable section fresh
variable {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam : ℝ) {m : ℕ}

/-- Shifting `y` by a multiple of `b^{st+D}` does not change the first `t` steps. -/
lemma local_shift (y δ : ZMod (b ^ m)) (t : ℕ) (hK : s * t + D ≤ m) :
    ∀ j ≤ t, GG K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) j = GG K lam y j ∧
      RR K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) j = RR K lam y j + (b : ZMod (b ^ m)) ^ (s * t + D) * δ := by
  intro j hj
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hG, hR⟩ := ih (by omega)
    have hjk : s * j + (D + s) ≤ s * t + D := by
      have := Nat.mul_le_mul_left s (show j + 1 ≤ t by omega); rw [mul_add, mul_one] at this; omega
    have hZ : ZZ K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) j = ZZ K lam y j := by
      show win (s * j) (D + s) ((r : ZMod (b ^ m)) ^ GG K lam _ j * RR K lam _ j) =
        win (s * j) (D + s) ((r : ZMod (b ^ m)) ^ GG K lam y j * RR K lam y j)
      rw [hG, hR, mul_add, mul_left_comm, win_add_high hjk hK]
    refine ⟨?_, ?_⟩
    · rw [GG_succ, GG_succ, hG, hh, hh, hZ]
    · rw [RR_succ, RR_succ, hR, hG, CC, CC, hZ]; ring

/-- At step `t` the shift moves the fresh block only. -/
lemma ZZ_shift (y δ : ZMod (b ^ m)) (t : ℕ) (hk : s * t + (D + s) ≤ m) :
    GG K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) t = GG K lam y t ∧
    XX K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) t = XX K lam y t ∧
    ZZ K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) t =
      ZZ K lam y t + (b : ZMod (b ^ (D + s))) ^ D * ((((r : ZMod (b ^ m)) ^ GG K lam y t * δ).val : ℕ) : ZMod (b ^ (D + s))) := by
  have hK : s * t + D ≤ m := by omega
  obtain ⟨hG, hR⟩ := local_shift K lam y δ t hK t le_rfl
  refine ⟨hG, ?_, ?_⟩
  · show win (s * t) D ((r : ZMod (b ^ m)) ^ GG K lam _ t * RR K lam _ t) =
      win (s * t) D ((r : ZMod (b ^ m)) ^ GG K lam y t * RR K lam y t)
    rw [hG, hR, mul_add, mul_left_comm, win_add_high (by omega) hK]
  show win (s * t) (D + s) ((r : ZMod (b ^ m)) ^ GG K lam _ t * RR K lam _ t) = _
  have e : (r : ZMod (b ^ m)) ^ GG K lam y t * (RR K lam y t + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) =
      WW K lam y t + (b : ZMod (b ^ m)) ^ (s * t) * ((b : ZMod (b ^ m)) ^ D * ((r : ZMod (b ^ m)) ^ GG K lam y t * δ)) := by
    show _ = (r : ZMod (b ^ m)) ^ GG K lam y t * RR K lam y t + _
    rw [pow_add]; ring
  rw [hG, hR, e, win_add hk, val_cast_eq_red (m := m) (j := D + s) (by omega),
    val_cast_eq_red (m := m) (j := D + s) (by omega), map_mul, map_pow, map_natCast]

/-- Averaging over the fresh block (with a shift-invariant weight `ψ`). -/
lemma average (hr : Nat.Coprime r b) (t : ℕ) (hk : s * t + (D + s) ≤ m)
    (ψ : ZMod (b ^ m) → ℝ) (hψ : ∀ y δ, ψ (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) = ψ y)
    (φ : ℕ → ZMod (b ^ D) → ℝ) (F : ZMod (b ^ (D + s)) → ℝ) :
    ((b : ℝ) ^ s) * ∑ y : ZMod (b ^ m), ψ y * φ (GG K lam y t) (XX K lam y t) * F (ZZ K lam y t) =
      ∑ y : ZMod (b ^ m), ψ y * φ (GG K lam y t) (XX K lam y t) *
        ∑ u : ZMod (b ^ s), F (liftz b s D (XX K lam y t) u) := by
  have hsm : s ≤ m := by omega
  have hcard : ((b : ℝ) ^ s) = ∑ _δ : ZMod (b ^ s), (1 : ℝ) := by simp [ZMod.card]
  rw [hcard, sum_mul, one_mul]
  have step1 : ∀ δ : ZMod (b ^ s),
      ∑ y : ZMod (b ^ m), ψ y * φ (GG K lam y t) (XX K lam y t) * F (ZZ K lam y t) =
      ∑ y : ZMod (b ^ m), ψ y * φ (GG K lam y t) (XX K lam y t) *
        F (ZZ K lam y t + (b : ZMod (b ^ (D + s))) ^ D *
          ((((r : ZMod (b ^ m)) ^ GG K lam y t * ((δ.val : ℕ) : ZMod (b ^ m))).val : ℕ) : ZMod (b ^ (D + s)))) := by
    intro δ
    refine (Fintype.sum_equiv (Equiv.addRight ((b : ZMod (b ^ m)) ^ (s * t + D) * ((δ.val : ℕ) : ZMod (b ^ m)))) _ _
      (fun y => ?_)).symm
    obtain ⟨hG, hX, hZ⟩ := ZZ_shift K lam y ((δ.val : ℕ) : ZMod (b ^ m)) t hk
    simp only [Equiv.coe_addRight]
    rw [hG, hX, hZ, hψ]
  rw [sum_congr rfl (fun δ _ => step1 δ), sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  rw [← mul_sum, ← lowD_ZZ K lam y t]
  congr 1
  refine fiber s D F (ZZ K lam y t) _ (isUnit_rpow hr s (GG K lam y t)) _ (fun δ => ?_)
  rw [val_cast_eq_red hsm, map_mul, map_pow, map_natCast, ← val_cast_eq_red hsm, ZMod.val_natCast,
    natCast_mod_pow hsm, ZMod.natCast_zmod_val]

end fresh


/-! ## The exponential potential (weighted by viability of the start) -/

lemma exp_le_quad {w : ℝ} (hw : |w| ≤ 1) : Real.exp w ≤ 1 + w + w ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hw
  have h2 := le_abs_self (Real.exp w - 1 - w)
  linarith

/-- Next-state value as a function of the `(D+s)`-window. -/
noncomputable abbrev Fz {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam θ : ℝ) (z : ZMod (b ^ (D + s))) : ℝ :=
  Real.exp (θ * ((K.hgt z : ℝ) + K.V (nxt b r s D (K.ch z) (K.hgt z) z) - lam))

/-- The certificate drift, exponentiated (at viable states). -/
lemma drift_exp {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam θ B : ℝ) (hB : ∀ x, |K.V x| ≤ B)
    (hθ : 0 ≤ θ) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1) (x : ZMod (b ^ D)) (hx : x ∈ K.W) :
    ∑ u : ZMod (b ^ s), Fz K lam θ (liftz b s D x u) ≤
      (b : ℝ) ^ s * Real.exp (θ * (K.V x + K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) := by
  set R : ℝ := (H : ℝ) + 2 * B + |K.g| with hR
  set a : ZMod (b ^ s) → ℝ := fun u => (K.hgt (liftz b s D x u) : ℝ) +
    K.V (nxt b r s D (K.ch (liftz b s D x u)) (K.hgt (liftz b s D x u)) (liftz b s D x u)) with ha
  set C : ℝ := θ * (K.V x + K.g - lam) with hC
  have hW : ∀ u, |a u - K.V x - K.g| ≤ R := by
    intro u
    have h1 := abs_le.mp (hB (nxt b r s D (K.ch (liftz b s D x u)) (K.hgt (liftz b s D x u)) (liftz b s D x u)))
    have h2 := abs_le.mp (hB x)
    have h3 : (K.hgt (liftz b s D x u) : ℝ) ≤ H := by exact_mod_cast K.hgt_le _
    have h4 : (0 : ℝ) ≤ K.hgt (liftz b s D x u) := Nat.cast_nonneg _
    have h5 := le_abs_self K.g
    have h6 := neg_abs_le K.g
    rw [abs_le]; simp only [ha]; constructor <;> linarith
  have key : ∀ u, Fz K lam θ (liftz b s D x u) ≤ Real.exp C * (1 + θ * (a u - K.V x - K.g) + θ ^ 2 * R ^ 2) := by
    intro u
    have e : Fz K lam θ (liftz b s D x u) = Real.exp C * Real.exp (θ * (a u - K.V x - K.g)) := by
      rw [Fz, ← Real.exp_add]; congr 1; simp only [hC, ha]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hw : |θ * (a u - K.V x - K.g)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hθ]
      exact le_trans (mul_le_mul_of_nonneg_left (hW u) hθ) hθR
    refine le_trans (exp_le_quad hw) ?_
    have : (θ * (a u - K.V x - K.g)) ^ 2 ≤ θ ^ 2 * R ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.mp (hW u)).1 (abs_le.mp (hW u)).2) (sq_nonneg θ)
    linarith
  have hsum : ∑ u : ZMod (b ^ s), a u ≤ (b : ℝ) ^ s * (K.V x + K.g) := by
    have := K.drift x hx; push_cast at this; exact this
  calc ∑ u : ZMod (b ^ s), Fz K lam θ (liftz b s D x u)
      ≤ ∑ u : ZMod (b ^ s), Real.exp C * (1 + θ * (a u - K.V x - K.g) + θ ^ 2 * R ^ 2) := sum_le_sum (fun u _ => key u)
    _ = Real.exp C * ((b : ℝ) ^ s * (1 + θ ^ 2 * R ^ 2) + θ * (∑ u : ZMod (b ^ s), a u - (b : ℝ) ^ s * (K.V x + K.g))) := by
        rw [← mul_sum]; congr 1
        simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        push_cast; ring
    _ ≤ Real.exp C * ((b : ℝ) ^ s * (1 + θ ^ 2 * R ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : θ * (∑ u : ZMod (b ^ s), a u - (b : ℝ) ^ s * (K.V x + K.g)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hθ (by linarith)
        linarith
    _ ≤ Real.exp C * ((b : ℝ) ^ s * Real.exp (θ ^ 2 * R ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := Real.add_one_le_exp (θ ^ 2 * R ^ 2); linarith
    _ = _ := by rw [Real.exp_add]; ring

noncomputable section potential
variable {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam : ℝ) {m : ℕ}

/-- The potential `Ψ_t = exp(θ (G_t - tλ + V(X_t)))`. -/
def Psi (θ : ℝ) (y : ZMod (b ^ m)) (t : ℕ) : ℝ :=
  Real.exp (θ * ((GG K lam y t : ℝ) - t * lam + K.V (XX K lam y t)))

/-- Viability of the start, as a real weight. -/
def psiW (y : ZMod (b ^ m)) : ℝ := if XX K lam y 0 ∈ K.W then 1 else 0

lemma psiW_shift (y δ : ZMod (b ^ m)) (t : ℕ) (hK : s * t + D ≤ m) :
    psiW K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) = psiW K lam y := by
  unfold psiW
  have : XX K lam (y + (b : ZMod (b ^ m)) ^ (s * t + D) * δ) 0 = XX K lam y 0 := by
    show win (s * 0) D ((r : ZMod (b ^ m)) ^ GG K lam _ 0 * RR K lam _ 0) =
      win (s * 0) D ((r : ZMod (b ^ m)) ^ GG K lam y 0 * RR K lam y 0)
    simp only [GG_zero, pow_zero, one_mul]
    show win (s * 0) D (y + _) = win (s * 0) D y
    exact win_add_high (by omega) hK _ _
  rw [this]

lemma Psi_step {N : ℕ} (hr : Nat.Coprime r b) (hm : s * N + (D + s) ≤ m) (hlam : 0 ≤ lam) (θ B : ℝ)
    (hθ : 0 ≤ θ) (hB : ∀ x, |K.V x| ≤ B) (y : ZMod (b ^ m)) (hy : XX K lam y 0 ∈ K.W) (t : ℕ) (ht : t < N) :
    Psi K lam θ y (t + 1) ≤
      Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t) + Real.exp (θ * (1 + B)) := by
  obtain ⟨hd, hW⟩ := invariant K lam y hr hm hy t (by omega)
  obtain ⟨_, hX⟩ := inv_step K lam y hr hm t ht hd hW
  rcases max_choice (GG K lam y t + hh K lam y t) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ with h | h
  · have hpad : GG K lam y (t + 1) = GG K lam y t + hh K lam y t := by rw [GG_succ, h]
    rw [hpad, show GG K lam y t + hh K lam y t - GG K lam y t - hh K lam y t = 0 by omega, pow_zero, one_mul] at hX
    have e : Psi K lam θ y (t + 1) =
        Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t) := by
      rw [Psi, hX, hpad, Fz, ← Real.exp_add]; congr 1; push_cast; ring
    rw [e]; linarith [Real.exp_pos (θ * (1 + B))]
  · have hG : GG K lam y (t + 1) = ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ := by rw [GG_succ, h]
    have hc := Nat.ceil_lt_add_one (show 0 ≤ ((t + 1 : ℕ) : ℝ) * lam by positivity)
    have hle : Psi K lam θ y (t + 1) ≤ Real.exp (θ * (1 + B)) := by
      rw [Psi]
      apply Real.exp_le_exp.mpr
      refine mul_le_mul_of_nonneg_left ?_ hθ
      rw [hG]
      have := (abs_le.mp (hB (XX K lam y (t + 1)))).2
      push_cast at hc ⊢
      linarith
    have : 0 ≤ Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t) := by positivity
    linarith

lemma Psi_sum_step {N : ℕ} (hr : Nat.Coprime r b) (hm : s * N + (D + s) ≤ m) (hlam : 0 ≤ lam) (θ B : ℝ)
    (hθ : 0 ≤ θ) (hB : ∀ x, |K.V x| ≤ B) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1) (t : ℕ) (ht : t < N) :
    ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y (t + 1) ≤
      Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) *
        ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y t
        + (∑ y : ZMod (b ^ m), psiW K lam y) * Real.exp (θ * (1 + B)) := by
  set ρ := Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2)
  have hk : s * t + (D + s) ≤ m := by
    have := Nat.mul_le_mul_left s (show t + 1 ≤ N by omega); rw [mul_add, mul_one] at this; omega
  have h1 : ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y (t + 1) ≤
      ∑ y : ZMod (b ^ m), psiW K lam y * (Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t))
        + (∑ y : ZMod (b ^ m), psiW K lam y) * Real.exp (θ * (1 + B)) := by
    rw [sum_mul, ← sum_add_distrib]
    refine sum_le_sum (fun y _ => ?_)
    unfold psiW; split_ifs with hy
    · have := Psi_step K lam hr hm hlam θ B hθ hB y hy t ht; linarith
    · simp
  have h2 := average K lam hr t hk (psiW K lam) (fun y δ => psiW_shift K lam y δ t (by omega))
    (fun G _ => Real.exp (θ * ((G : ℝ) - t * lam))) (Fz K lam θ)
  have h3 : ((b : ℝ) ^ s) * ∑ y : ZMod (b ^ m), psiW K lam y * Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t)
      ≤ (b : ℝ) ^ s * (ρ * ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y t) := by
    rw [h2, mul_sum, mul_sum]
    refine sum_le_sum (fun y _ => ?_)
    unfold psiW; split_ifs with hy
    · obtain ⟨_, hW⟩ := invariant K lam y hr hm hy t (by omega)
      have hd := drift_exp K lam θ B hB hθ hθR (XX K lam y t) hW
      simp only [one_mul]
      calc Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * ∑ u : ZMod (b ^ s), Fz K lam θ (liftz b s D (XX K lam y t) u)
          ≤ Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) *
            ((b : ℝ) ^ s * Real.exp (θ * (K.V (XX K lam y t) + K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2)) :=
            mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
        _ = (b : ℝ) ^ s * (ρ * Psi K lam θ y t) := by
            rw [Psi]; simp only [ρ, ← Real.exp_add]; rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    · simp
  have h3' : ∑ y : ZMod (b ^ m), psiW K lam y * (Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t))
      ≤ ρ * ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y t := by
    have hb0 : (0 : ℝ) < (b : ℝ) ^ s := by
      have : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne b)
      positivity
    refine le_of_mul_le_mul_left ?_ hb0
    simpa only [mul_assoc] using h3
  linarith

end potential


/-! ## Most viable starts are admissible; counting -/

noncomputable section counting
variable {b r s D H : ℕ} [NeZero b] (K : Cert b r s D H) (lam : ℝ) {m : ℕ}

lemma psiW_nonneg (y : ZMod (b ^ m)) : 0 ≤ psiW K lam y := by unfold psiW; split_ifs <;> norm_num

lemma sumPsi_le {N : ℕ} (hr : Nat.Coprime r b) (hm : s * N + (D + s) ≤ m) (hlam : 0 ≤ lam) (θ B : ℝ)
    (hθ : 0 ≤ θ) (hB : ∀ x, |K.V x| ≤ B) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1)
    (hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) < 1) :
    ∀ t ≤ N, ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y t ≤
      (∑ y : ZMod (b ^ m), psiW K lam y) * (Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))) := by
  set ρ := Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2)
  set K0 := Real.exp (θ * (1 + B))
  set S := ∑ y : ZMod (b ^ m), psiW K lam y
  have hS : 0 ≤ S := sum_nonneg (fun y _ => psiW_nonneg K lam y)
  have h1ρ : 0 < 1 - ρ := by linarith
  have hK0 : 0 ≤ K0 / (1 - ρ) := div_nonneg (Real.exp_pos _).le h1ρ.le
  intro t ht
  induction t with
  | zero =>
    calc ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y 0 ≤ ∑ y : ZMod (b ^ m), psiW K lam y * Real.exp (θ * B) := by
          refine sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left ?_ (psiW_nonneg K lam y))
          rw [Psi, GG_zero]
          apply Real.exp_le_exp.mpr
          have := (abs_le.mp (hB (XX K lam y 0))).2
          push_cast; nlinarith
      _ = S * Real.exp (θ * B) := by rw [← sum_mul]
      _ ≤ _ := by gcongr; linarith
  | succ t ih =>
    have hs := Psi_sum_step K lam hr hm hlam θ B hθ hB hθR t (by omega)
    have ih' := ih (by omega)
    have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
    have hmul : (1 - ρ) * (K0 / (1 - ρ)) = K0 := mul_div_cancel₀ _ (ne_of_gt h1ρ)
    have hexp : 0 ≤ Real.exp (θ * B) := (Real.exp_pos _).le
    calc ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y (t + 1)
        ≤ ρ * ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y t + S * K0 := hs
      _ ≤ ρ * (S * (Real.exp (θ * B) + K0 / (1 - ρ))) + S * K0 := by gcongr
      _ ≤ S * (Real.exp (θ * B) + K0 / (1 - ρ)) := by
          have : ρ * (Real.exp (θ * B) + K0 / (1 - ρ)) + K0 ≤ Real.exp (θ * B) + K0 / (1 - ρ) := by nlinarith
          nlinarith

/-- Markov's inequality on the potential, over viable starts. -/
lemma card_bad_mul_le (θ B c₀ : ℝ) (hB : ∀ x, |K.V x| ≤ B) (hθ : 0 ≤ θ) (t : ℕ) :
    ((univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W ∧ c₀ < (GG K lam y t : ℝ) - t * lam)).card : ℝ) *
      Real.exp (θ * (c₀ - B)) ≤ ∑ y : ZMod (b ^ m), psiW K lam y * Psi K lam θ y t := by
  set bad := univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W ∧ c₀ < (GG K lam y t : ℝ) - t * lam)
  have h1 := card_nsmul_le_sum bad (fun y => psiW K lam y * Psi K lam θ y t) (Real.exp (θ * (c₀ - B))) (fun y hy => by
      simp only [bad, mem_filter, mem_univ, true_and] at hy
      rw [psiW, if_pos hy.1, one_mul, Psi]; apply Real.exp_le_exp.mpr
      have := (abs_le.mp (hB (XX K lam y t))).1
      apply mul_le_mul_of_nonneg_left _ hθ
      linarith [hy.2])
  rw [nsmul_eq_mul] at h1
  refine h1.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => ?_))
  exact mul_nonneg (psiW_nonneg K lam y) (Real.exp_pos _).le

lemma sum_psiW (m : ℕ) : ∑ y : ZMod (b ^ m), psiW K lam y =
    ((univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W)).card : ℝ) := by
  unfold psiW; rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]

/-- At least half of the viable starts have `G_N ≤ Nλ + c₀`. -/
lemma good_half {N : ℕ} (hr : Nat.Coprime r b) (hm : s * N + (D + s) ≤ m) (hlam : 0 ≤ lam) (θ B c₀ : ℝ)
    (hθ : 0 < θ) (hB : ∀ x, |K.V x| ≤ B) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1)
    (hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) < 1)
    (hc₀ : 2 * (Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))) ≤ Real.exp (θ * (c₀ - B))) :
    ((univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W)).card : ℝ) ≤
      2 * ((univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W ∧
        (GG K lam y N : ℝ) ≤ N * lam + c₀)).card : ℝ) := by
  set M₀ := Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))
  have hsum := sumPsi_le K lam hr hm hlam θ B hθ.le hB hθR hρ N le_rfl
  have hmk := card_bad_mul_le K lam θ B c₀ hB hθ.le N (m := m)
  rw [sum_psiW] at hsum
  set Y := univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W)
  set bad := univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W ∧ c₀ < (GG K lam y N : ℝ) - N * lam)
  set good := univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W ∧ (GG K lam y N : ℝ) ≤ N * lam + c₀)
  have hM0 : 0 < M₀ := by
    have : 0 < 1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) := by linarith
    positivity
  have hbad : (bad.card : ℝ) * 2 ≤ Y.card := by
    have : (bad.card : ℝ) * (2 * M₀) ≤ Y.card * M₀ :=
      calc (bad.card : ℝ) * (2 * M₀) ≤ bad.card * Real.exp (θ * (c₀ - B)) :=
            mul_le_mul_of_nonneg_left hc₀ (Nat.cast_nonneg _)
        _ ≤ _ := hmk.trans hsum
    nlinarith
  have hbad_eq : bad = Y.filter (fun y => c₀ < (GG K lam y N : ℝ) - N * lam) := by
    ext y; simp only [bad, Y, mem_filter, mem_univ, true_and]
  have hgood_eq : good = Y.filter (fun y => ¬ (c₀ < (GG K lam y N : ℝ) - N * lam)) := by
    ext y; simp only [good, Y, mem_filter, mem_univ, true_and, not_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  have hsplit : Y.card = bad.card + good.card := by
    rw [hbad_eq, hgood_eq, card_filter_add_card_filter_not]
  have : (Y.card : ℝ) = bad.card + good.card := by exact_mod_cast hsplit
  linarith

/-- Viable starts: at least `b^(m-D)` of them. -/
lemma card_viable_ge (hWne : K.W.Nonempty) (hDm : D ≤ m) :
    b ^ (m - D) ≤ (univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W)).card := by
  obtain ⟨x0, hx0⟩ := hWne
  have hb0 : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  let f : ZMod (b ^ (m - D)) → ZMod (b ^ m) := fun e => ((x0.val + b ^ D * e.val : ℕ) : ZMod (b ^ m))
  have hlt : ∀ e : ZMod (b ^ (m - D)), x0.val + b ^ D * e.val < b ^ m := by
    intro e
    have h1 := ZMod.val_lt x0; have h2 := ZMod.val_lt e
    have : b ^ m = b ^ D * b ^ (m - D) := by rw [← pow_add]; congr 1; omega
    rw [this]; nlinarith
  have hmap : ∀ e ∈ (univ : Finset (ZMod (b ^ (m - D)))), f e ∈ univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W) := by
    intro e _
    simp only [mem_filter, mem_univ, true_and]
    show win (s * 0) D ((r : ZMod (b ^ m)) ^ GG K lam (f e) 0 * RR K lam (f e) 0) ∈ K.W
    simp only [GG_zero, pow_zero, one_mul]
    show win (s * 0) D (f e) ∈ K.W
    rw [win, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt e), mul_zero, pow_zero, Nat.div_one]
    push_cast
    rw [natCast_pow_self_eq_zero, zero_mul, add_zero, ZMod.natCast_zmod_val]
    exact hx0
  have hinj : Set.InjOn f (univ : Finset (ZMod (b ^ (m - D)))) := by
    intro e _ e' _ h
    have h1 := congrArg ZMod.val h
    simp only [f, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt e), Nat.mod_eq_of_lt (hlt e')] at h1
    have h2 : e.val = e'.val := by
      have hpos : 0 < b ^ D := pow_pos hb0 D
      have := Nat.eq_of_mul_eq_mul_left hpos (by omega : b ^ D * e.val = b ^ D * e'.val)
      exact this
    exact ZMod.val_injective _ h2
  have := card_le_card_of_injOn f hmap hinj
  simpa [ZMod.card] using this

/-- Fibers of the reduction mod `b^j` have at most `b^(m-j)` elements. -/
lemma card_fiber_red_le {j : ℕ} (hj : j ≤ m) (S : Finset (ZMod (b ^ m))) (c : ZMod (b ^ j))
    (hS : ∀ y ∈ S, red j hj y = c) : S.card ≤ b ^ (m - j) := by
  have hb0 : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hbm : b ^ m = b ^ j * b ^ (m - j) := by rw [← pow_add]; congr 1; omega
  let g : ZMod (b ^ m) → ℕ := fun y => y.val / b ^ j
  have hmap : ∀ y ∈ S, g y ∈ range (b ^ (m - j)) := by
    intro y _
    rw [mem_range, Nat.div_lt_iff_lt_mul (pow_pos hb0 j), mul_comm, ← hbm]
    exact ZMod.val_lt y
  have hinj : Set.InjOn g S := by
    intro y hy y' hy' h
    have e1 := hS y hy; have e2 := hS y' hy'
    rw [← e2, ← val_cast_eq_red hj, ← val_cast_eq_red hj, ZMod.natCast_eq_natCast_iff'] at e1
    have hy1 := Nat.mod_add_div y.val (b ^ j); have hy2 := Nat.mod_add_div y'.val (b ^ j)
    have : y.val = y'.val := by
      simp only [g] at h
      rw [← hy1, ← hy2, e1, h]
    exact ZMod.val_injective _ this
  have := card_le_card_of_injOn g hmap hinj
  simpa using this

end counting


/-! ## Counting and density -/

/-- `n(y) ≤ Cst · (b^s)^N`. -/
noncomputable def Cst (b r s : ℕ) (lam c₀ : ℝ) : ℝ :=
  (b : ℝ) ^ s * (r : ℝ) ^ ((1 + (⌈c₀⌉₊ : ℝ))) * ((r : ℝ) ^ lam / ((b : ℝ) ^ s - (r : ℝ) ^ lam))

open Classical in
lemma count_N {b r s D H : ℕ} [NeZero b] (hb : 2 ≤ b) (hr2 : 2 ≤ r) (hcop : Nat.Coprime r b)
    (K : Cert b r s D H) (hWne : K.W.Nonempty) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : (r : ℝ) ^ lam < (b : ℝ) ^ s)
    (θ B c₀ : ℝ) (hθ : 0 < θ) (hB : ∀ x, |K.V x| ≤ B) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1)
    (hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) < 1)
    (hc₀ : 2 * (Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))) ≤ Real.exp (θ * (c₀ - B)))
    (N : ℕ) :
    b ^ (s * N) ≤ 2 * b ^ D *
      ((range (⌊Cst b r s lam c₀ * ((b : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable r b)).card := by
  set m := s * N + (D + s) with hmdef
  have hm : s * N + (D + s) ≤ m := le_rfl
  have hgood := good_half K lam (m := m) hcop hm hlam0 θ B c₀ hθ hB hθR hρ hc₀
  have hY := card_viable_ge K lam (m := m) hWne (by omega)
  set Y := univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W)
  set good := univ.filter (fun y : ZMod (b ^ m) => XX K lam y 0 ∈ K.W ∧ (GG K lam y N : ℝ) ≤ N * lam + c₀)
  set A : ℕ := ⌈(N : ℝ) * lam⌉₊ + ⌈c₀⌉₊ with hAdef
  have hA : ∀ y ∈ good, GG K lam y N ≤ A := by
    intro y hy
    simp only [good, mem_filter, mem_univ, true_and] at hy
    have h1 := Nat.le_ceil ((N : ℝ) * lam)
    have h2 := Nat.le_ceil c₀
    have : (GG K lam y N : ℝ) ≤ (A : ℝ) := by rw [hAdef]; push_cast; linarith
    exact_mod_cast this
  have hAD : (A : ℝ) ≤ N * lam + (1 + (⌈c₀⌉₊ : ℝ)) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) * lam by positivity)
    rw [hAdef]; push_cast; linarith
  set T := (range (⌊Cst b r s lam c₀ * ((b : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable r b)
  set f : ZMod (b ^ m) → ℕ := fun y => nval K lam y A N
  have hmaps : ∀ y ∈ good, f y ∈ T := by
    intro y hy
    simp only [T, mem_filter, mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), nval_representable K lam y hb hr2 hcop.symm (hA y hy)⟩
    have := nval_le_real K lam y hb hr2 (hA y hy) hlam _ hAD
    refine this.trans (le_of_eq ?_)
    rw [Cst]; ring
  have hsN : s * N ≤ m := by omega
  have hfib : ∀ n ∈ good.image f, (good.filter (fun y => f y = n)).card ≤ b ^ (m - s * N) := by
    intro n hn
    obtain ⟨y0, hy0, rfl⟩ := mem_image.mp hn
    refine card_fiber_red_le (j := s * N) hsN _ (red (s * N) hsN y0) (fun y hy => ?_)
    simp only [mem_filter] at hy
    have hy0' := hy0; have hy' := hy.1
    simp only [good, mem_filter, mem_univ, true_and] at hy0' hy'
    exact nval_inj K lam hcop hm hy'.1 hy0'.1 (hA y hy.1) (hA y0 hy0) hy.2
  have h1 := card_le_mul_card_image good (b ^ (m - s * N)) hfib
  have h2 : (good.image f).card ≤ T.card := card_le_card (fun n hn => by
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hn; exact hmaps y hy)
  have hgood' : Y.card ≤ 2 * good.card := by exact_mod_cast hgood
  -- combine:  b^(m-D) ≤ |Y| ≤ 2|good| ≤ 2 b^(m-sN) |T|
  have hc : b ^ (m - D) ≤ 2 * b ^ (m - s * N) * T.card := by
    calc b ^ (m - D) ≤ Y.card := hY
      _ ≤ 2 * good.card := hgood'
      _ ≤ 2 * (b ^ (m - s * N) * (good.image f).card) := by omega
      _ ≤ 2 * b ^ (m - s * N) * T.card := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
  have e1 : m - D = s * N + s := by omega
  have e2 : m - s * N = D + s := by omega
  rw [e1, e2, pow_add, pow_add] at hc
  have hbs : 0 < b ^ s := pow_pos (by omega) s
  have : b ^ (s * N) * b ^ s ≤ (2 * b ^ D * T.card) * b ^ s := by
    calc b ^ (s * N) * b ^ s ≤ 2 * (b ^ D * b ^ s) * T.card := hc
      _ = (2 * b ^ D * T.card) * b ^ s := by ring
  exact Nat.le_of_mul_le_mul_right this hbs

open Classical in
/-- **Main theorem (general bases, conditional on a certificate).** If a look-ahead potential
certificate with a nonempty viable set exists for digits in base `b` and other base `r`
(`b, r ≥ 2` coprime) with drift `g < λ` and `r^λ < b^s`, then the integers that are sums of
numbers `r^k b^l`, none dividing another, have positive lower density. -/
theorem pos_lower_density {b r s D H : ℕ} [NeZero b] (hb : 2 ≤ b) (hr2 : 2 ≤ r) (hcop : Nat.Coprime r b)
    (K : Cert b r s D H) (hWne : K.W.Nonempty) (lam : ℝ) (hlam0 : 0 ≤ lam) (hg : K.g < lam)
    (hlam : (r : ℝ) ^ lam < (b : ℝ) ^ s) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      c * x ≤ (((range (x + 1)).filter (Representable r b)).card : ℝ) := by
  set B : ℝ := ∑ x, |K.V x| + 1 with hBdef
  have hB : ∀ x, |K.V x| ≤ B := by
    intro x
    have := single_le_sum (f := fun x => |K.V x|) (fun x _ => abs_nonneg _) (mem_univ x)
    linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ x, |K.V x| := sum_nonneg (fun x _ => abs_nonneg _)
    linarith
  set R : ℝ := (H : ℝ) + 2 * B + |K.g| with hRdef
  have hR : 2 ≤ R := by have := abs_nonneg K.g; have : (0 : ℝ) ≤ H := Nat.cast_nonneg _; linarith
  set d : ℝ := lam - K.g with hd
  have hd0 : 0 < d := by linarith
  set θ : ℝ := min (1 / R) (d / (2 * R ^ 2)) with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθR : θ * R ≤ 1 := by
    have : θ ≤ 1 / R := min_le_left _ _
    calc θ * R ≤ 1 / R * R := by gcongr
      _ = 1 := by field_simp
  have hθd : θ * R ^ 2 ≤ d / 2 := by
    have : θ ≤ d / (2 * R ^ 2) := min_le_right _ _
    calc θ * R ^ 2 ≤ d / (2 * R ^ 2) * R ^ 2 := by gcongr
      _ = d / 2 := by field_simp
  have hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * R ^ 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have : θ ^ 2 * R ^ 2 ≤ θ * (d / 2) := by
      rw [pow_two, mul_assoc]; exact mul_le_mul_of_nonneg_left hθd hθ.le
    have : θ * (K.g - lam) = -(θ * d) := by rw [hd]; ring
    nlinarith
  set M₀ : ℝ := Real.exp (θ * B) + Real.exp (θ * (1 + B)) / (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * R ^ 2))
  have hM₀ : 0 < M₀ := by
    have : 0 < 1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * R ^ 2) := by linarith
    positivity
  set c₀ : ℝ := B + Real.log (2 * M₀) / θ
  have hc₀ : 2 * M₀ ≤ Real.exp (θ * (c₀ - B)) := by
    have : θ * (c₀ - B) = Real.log (2 * M₀) := by simp only [c₀]; field_simp; ring
    rw [this, Real.exp_log (by positivity)]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have h7 : (1 : ℝ) ≤ (r : ℝ) ^ lam := Real.one_le_rpow hr1 hlam0
  have hs1 : (1 : ℝ) < (b : ℝ) ^ s := lt_of_le_of_lt h7 hlam
  have hC : 0 < Cst b r s lam c₀ := by
    rw [Cst]; have : 0 < (b : ℝ) ^ s - (r : ℝ) ^ lam := by linarith
    have : (0 : ℝ) < (r : ℝ) ^ lam := by linarith
    have : (0 : ℝ) < r := by linarith
    positivity
  set C := Cst b r s lam c₀
  have hcount := count_N hb hr2 hcop K hWne lam hlam0 hlam θ B c₀ hθ hB hθR hρ hc₀
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbD : (0 : ℝ) < (b : ℝ) ^ D := by positivity
  refine ⟨1 / (2 * (b : ℝ) ^ D * C * (b : ℝ) ^ s), by positivity, ⌈C * ((b : ℝ) ^ s) ^ 1⌉₊, fun x hx => ?_⟩
  have hx' : C * ((b : ℝ) ^ s) ^ 1 ≤ (x : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx)
  have hex : ∃ n, (x : ℝ) < C * ((b : ℝ) ^ s) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((x : ℝ) / C) hs1
    refine ⟨n, ?_⟩
    have : ((b : ℝ) ^ s) ^ n ≤ ((b : ℝ) ^ s) ^ (n + 1) := pow_le_pow_right₀ hs1.le (Nat.le_succ n)
    rw [div_lt_iff₀ hC] at hn
    nlinarith
  classical
  set N := Nat.find hex
  have hNx : (x : ℝ) < C * ((b : ℝ) ^ s) ^ (N + 1) := Nat.find_spec hex
  have hN1 : 1 ≤ N := by
    by_contra hlt
    push Not at hlt
    have : N = 0 := by omega
    rw [this, zero_add] at hNx
    linarith
  have hxN : C * ((b : ℝ) ^ s) ^ N ≤ (x : ℝ) := by
    have := Nat.find_min hex (show N - 1 < N by omega)
    push Not at this
    rwa [show N - 1 + 1 = N by omega] at this
  have hcN := hcount N
  have hmono : ((range (⌊C * ((b : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable r b)).card ≤
      ((range (x + 1)).filter (Representable r b)).card := by
    have hfl : ⌊C * ((b : ℝ) ^ s) ^ N⌋₊ ≤ x := Nat.floor_le_of_le hxN
    exact card_le_card (filter_subset_filter _ (range_subset_range.mpr (Nat.succ_le_succ hfl)))
  have hcN' : ((b : ℝ) ^ s) ^ N ≤ 2 * (b : ℝ) ^ D * (((range (x + 1)).filter (Representable r b)).card : ℝ) := by
    have h1 : ((b ^ (s * N) : ℕ) : ℝ) ≤ ((2 * b ^ D * ((range (x + 1)).filter (Representable r b)).card : ℕ) : ℝ) := by
      exact_mod_cast le_trans hcN (Nat.mul_le_mul_left _ hmono)
    push_cast at h1
    rwa [pow_mul] at h1
  have hpos : (0 : ℝ) < 2 * (b : ℝ) ^ D * C * (b : ℝ) ^ s := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  rw [pow_succ] at hNx
  nlinarith

/-! ## The (4,3) instance: the only external input is the certificate checked by `verifyd.c` -/

lemma three_rpow_lt : (3 : ℝ) ^ ((58 : ℝ) / 23) < (4 : ℝ) ^ 2 := by
  by_contra h
  push Not at h
  have h1 : ((4 : ℝ) ^ 2) ^ 23 ≤ ((3 : ℝ) ^ ((58 : ℝ) / 23)) ^ 23 := pow_le_pow_left₀ (by positivity) h 23
  rw [← Real.rpow_natCast ((3 : ℝ) ^ ((58 : ℝ) / 23)), ← Real.rpow_mul (by norm_num),
    show (58 : ℝ) / 23 * ((23 : ℕ) : ℝ) = ((58 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  -- 3^58 = (3^29)^2 < (4^23)^2 = (4^2)^23, from 3^29 < 4^23
  have h2 : (3 : ℝ) ^ 58 < ((4 : ℝ) ^ 2) ^ 23 := by
    have e1 : (3 : ℝ) ^ 58 = ((3 : ℝ) ^ 29) ^ 2 := by rw [← pow_mul]
    have e2 : ((4 : ℝ) ^ 2) ^ 23 = ((4 : ℝ) ^ 23) ^ 2 := by rw [← pow_mul, ← pow_mul]
    rw [e1, e2]
    exact pow_lt_pow_left₀ (by norm_num) (by positivity) (by norm_num)
  exact absurd h1 (not_le.mpr h2)

open Classical in
/-- **Erdős #1110, (4,3), conditional on the machine-checked certificate.** If there is a
certificate with base-4 digits, blocks of `s = 2` digits, `D = 14`-digit states, heights `≤ 18`,
a nonempty viable set and drift `g = 42192162 / (16 · 2^20)` (what `verifyd.c` checks for the table
`V43_final.bin`), then the integers that are sums of numbers `4^k 3^l`, none dividing another, have
positive lower density. -/
theorem erdos1110_43_density (h : ∃ K : Cert 4 3 2 14 18, K.W.Nonempty ∧ K.g = 42192162 / (16 * 2 ^ 20)) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      c * x ≤ (((range (x + 1)).filter (Representable 4 3)).card : ℝ) := by
  obtain ⟨K, hW, hK⟩ := h
  obtain ⟨c, hc, x₀, hx⟩ := pos_lower_density (by norm_num) (by norm_num) (by norm_num) K hW ((58 : ℝ) / 23)
    (by norm_num) (by rw [hK]; norm_num) (by push_cast; exact three_rpow_lt)
  refine ⟨c, hc, x₀, fun x hxx => ?_⟩
  have := hx x hxx
  have e : (range (x + 1)).filter (Representable 3 4) = (range (x + 1)).filter (Representable 4 3) := by
    ext n; simp only [mem_filter, representable_comm]
  rwa [e] at this

/-- Sanity check: the general `Cert` structure is inhabited (toy certificate with a useless drift). -/
def toyCert : Cert 2 3 1 1 1 where
  W := univ
  ch z := if z.val % 2 = 1 then {(0, 0)} else ∅
  hgt z := if z.val % 2 = 1 then 1 else 0
  V _ := 0
  g := 1
  chain z a ha c hc h := by split_ifs at ha hc <;> simp_all
  inj z a ha c hc h := by split_ifs at ha hc <;> simp_all
  alpha_lt z a ha := by split_ifs at ha <;> simp_all
  gamma_lt z a ha := by split_ifs at ha with h <;> simp_all
  hgt_le z := by split_ifs <;> norm_num
  res z _ := by
    revert z
    simp only [vD, cval]
    decide
  closed _ _ := mem_univ _
  rclosed _ _ := mem_univ _
  drift x _ := by
    simp only [add_zero, zero_add]
    have : ∀ u : ZMod (2 ^ 1), ((if (liftz 2 1 1 x u).val % 2 = 1 then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      intro u; split_ifs <;> norm_num
    calc _ ≤ ∑ _u : ZMod (2 ^ 1), (1 : ℝ) := sum_le_sum (fun u _ => this u)
      _ = ((2 : ℕ) : ℝ) ^ 1 * 1 := by simp [ZMod.card]

end E1110G

#print axioms E1110G.pos_lower_density
#print axioms E1110G.erdos1110_43_density
