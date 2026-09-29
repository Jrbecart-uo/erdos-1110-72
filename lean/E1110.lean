import Mathlib

/-!
# Erdős #1110, (p,q) = (7,2): positive lower density, reduced to a finite certificate

Formalizes Theorem A of `erdos/1110/NOTE.md`: a two-block look-ahead potential certificate
(`Cert s H`) with drift `g < λ` and `7^λ < 2^s` implies that the integers representable as sums
of `7^k 2^l`, none dividing another, have positive lower density (`pos_lower_density`).
`erdos1110_72_density` instantiates `s = 11`, `H = 10`, `λ = 286/73`, leaving as the only
external input the existence of the certificate that `verify.c` and `verify2.c` check
(`g = 8385274094 / 2^31` for the table `V_s11_it8.bin`). The certificate itself (2^22 states)
is NOT checked in Lean.

`Representable` is copied verbatim from formal-conjectures (`Erdos1110.Representable`,
`Erdos246.Gamma`).

Proof structure: the encoding runs in `ZMod (2^(sN))` (`proc`); `win` extracts digit windows;
`average` replaces conditional expectation by averaging over translations
`y ↦ y + 2^{s(t+2)} δ`; the exponential potential `Psi` gives the Markov bound (`good_half`).
-/

open Finset

namespace E1110

/-- `Erdos246.Gamma` from formal-conjectures, verbatim. -/
def Gamma (a b : ℕ) : Set ℕ := {x | ∃ k l : ℕ, x = a ^ k * b ^ l}

/-- `Erdos1110.Representable` from formal-conjectures, verbatim. -/
def Representable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Gamma p q ∧ IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n

/-- Bits `[k, k+j)` of `w`, as an element of `ZMod (2^j)`. -/
def win {m : ℕ} (k j : ℕ) (w : ZMod (2 ^ m)) : ZMod (2 ^ j) := ((w.val / 2 ^ k : ℕ) : ZMod (2 ^ j))

lemma natCast_mod_pow {m j : ℕ} (h : j ≤ m) (a : ℕ) :
    (((a % 2 ^ m : ℕ)) : ZMod (2 ^ j)) = (a : ZMod (2 ^ j)) := by
  rw [ZMod.natCast_eq_natCast_iff']
  exact Nat.mod_mod_of_dvd a (pow_dvd_pow 2 h)

lemma nat_win (Y k j m : ℕ) (h : k + j ≤ m) :
    (((Y % 2 ^ m) / 2 ^ k : ℕ) : ZMod (2 ^ j)) = ((Y / 2 ^ k : ℕ) : ZMod (2 ^ j)) := by
  have hm : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by rw [← pow_add]; congr 1; omega
  rw [hm, Nat.mod_mul_right_div_self]
  exact natCast_mod_pow (by omega) _

/-- The reduction `ZMod (2^m) → ZMod (2^j)` written with `val`, as a ring hom. -/
lemma val_cast_eq_castHom {m j : ℕ} (h : j ≤ m) (a : ZMod (2 ^ m)) :
    ((a.val : ℕ) : ZMod (2 ^ j)) = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ j)) a := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

/-- Core lemma: adding a multiple of `2^k` shifts the window by the multiplier. -/
lemma win_add {m k j : ℕ} (h : k + j ≤ m) (x e : ZMod (2 ^ m)) :
    win k j (x + 2 ^ k * e) = win k j x + (e.val : ZMod (2 ^ j)) := by
  have hx : x + 2 ^ k * e = ((x.val + 2 ^ k * e.val : ℕ) : ZMod (2 ^ m)) := by
    push_cast; simp only [ZMod.natCast_zmod_val]
  unfold win
  rw [hx, ZMod.val_natCast, nat_win _ _ _ _ h, Nat.add_mul_div_left _ _ (by positivity)]
  push_cast
  rfl

lemma win_zero {m k j : ℕ} : win k j (0 : ZMod (2 ^ m)) = 0 := by
  simp [win]

lemma win_two_pow_mul {m k j : ℕ} (h : k + j ≤ m) (e : ZMod (2 ^ m)) :
    win k j (2 ^ k * e) = (e.val : ZMod (2 ^ j)) := by
  simpa [win_zero] using win_add h 0 e

/-- Adding a multiple of `2^K` with `K ≥ k + j` does not change the window. -/
lemma win_add_high {m k j K : ℕ} (h : k + j ≤ K) (hK : K ≤ m) (x e : ZMod (2 ^ m)) :
    win k j (x + 2 ^ K * e) = win k j x := by
  have hK' : 2 ^ K * e = 2 ^ k * (2 ^ (K - k) * e) := by
    rw [← mul_assoc, ← pow_add]; congr 2; omega
  rw [hK', win_add (by omega), val_cast_eq_castHom (by omega)]
  simp only [map_mul, map_pow, map_ofNat]
  have : (2 : ZMod (2 ^ j)) ^ (K - k) = 0 := by
    have hd : (2 : ZMod (2 ^ j)) ^ (K - k) = 2 ^ j * 2 ^ (K - k - j) := by
      rw [← pow_add]; congr 1; omega
    rw [hd]
    have : ((2 ^ j : ℕ) : ZMod (2 ^ j)) = 0 := ZMod.natCast_self _
    push_cast at this
    rw [this, zero_mul]
  rw [this, zero_mul, add_zero]

/-- Multiplying a multiple of `2^k` by `c` multiplies the window by `c`. -/
lemma win_mul {m k j : ℕ} (h : k + j ≤ m) (c r : ZMod (2 ^ m)) :
    win k j (c * (2 ^ k * r)) = (c.val : ZMod (2 ^ j)) * win k j (2 ^ k * r) := by
  rw [mul_left_comm, win_two_pow_mul h, win_two_pow_mul h, val_cast_eq_castHom (by omega),
    val_cast_eq_castHom (by omega), val_cast_eq_castHom (by omega), map_mul]

/-- Nested windows. -/
lemma win_win {m k s : ℕ} (h : k + 3 * s ≤ m) (x : ZMod (2 ^ m)) :
    win (k + s) (2 * s) x = ((((win k (3 * s) x).val / 2 ^ s : ℕ)) : ZMod (2 ^ (2 * s))) := by
  unfold win
  rw [ZMod.val_natCast]
  have h3 : 2 ^ (3 * s) = 2 ^ s * 2 ^ (2 * s) := by rw [← pow_add]; congr 1; omega
  rw [h3, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add]
  exact (natCast_mod_pow le_rfl _).symm


/-! ## 7⁻¹, chain values, reductions -/

lemma coprime7 (m : ℕ) : Nat.Coprime 7 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)

/-- `7⁻¹` in `ZMod (2^m)`. -/
def inv7 (m : ℕ) : ZMod (2 ^ m) := ((ZMod.unitOfCoprime 7 (coprime7 m))⁻¹ : (ZMod (2 ^ m))ˣ)

lemma seven_mul_inv7 (m : ℕ) : (7 : ZMod (2 ^ m)) * inv7 m = 1 := by
  have := (ZMod.unitOfCoprime 7 (coprime7 m)).mul_inv
  rw [ZMod.coe_unitOfCoprime] at this
  simpa only [inv7, Nat.cast_ofNat] using this

lemma pow7_mul_inv7 (m G : ℕ) : (7 : ZMod (2 ^ m)) ^ G * inv7 m ^ G = 1 := by
  rw [← mul_pow, seven_mul_inv7, one_pow]

/-- Reduction `ZMod (2^m) → ZMod (2^j)`. -/
abbrev red {m : ℕ} (j : ℕ) (h : j ≤ m) : ZMod (2 ^ m) →+* ZMod (2 ^ j) :=
  ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ j))

lemma red_inv7 {m j : ℕ} (h : j ≤ m) : red j h (inv7 m) = inv7 j := by
  have h1 := congrArg (red j h) (seven_mul_inv7 m)
  rw [map_mul, map_one, map_ofNat] at h1
  calc red j h (inv7 m) = (inv7 j * 7) * red j h (inv7 m) := by
        rw [mul_comm (inv7 j), seven_mul_inv7, one_mul]
    _ = inv7 j := by rw [mul_assoc, h1, mul_one]

/-- Value of a chain `Σ 2^α i^γ` (with `i` standing for `7⁻¹`). -/
def cval {R : Type*} [CommRing R] (i : R) (C : Finset (ℕ × ℕ)) : R := ∑ a ∈ C, 2 ^ a.1 * i ^ a.2

lemma map_cval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (i : R) (C : Finset (ℕ × ℕ)) :
    f (cval i C) = cval (f i) C := by
  simp [cval, map_sum, map_ofNat]

lemma red_cval {m j : ℕ} (h : j ≤ m) (C : Finset (ℕ × ℕ)) :
    red j h (cval (inv7 m) C) = cval (inv7 j) C := by
  rw [map_cval, red_inv7]

lemma win_red {m k j j' : ℕ} (h : j' ≤ j) (x : ZMod (2 ^ m)) :
    red j' h (win k j x) = win k j' x := by
  rw [← val_cast_eq_castHom h, win, ZMod.val_natCast, natCast_mod_pow h]
  rfl

lemma exists_eq_two_pow_mul {m j : ℕ} (h : j ≤ m) (a : ZMod (2 ^ m)) (ha : red j h a = 0) :
    ∃ e, a = 2 ^ j * e := by
  rw [← val_cast_eq_castHom h, ZMod.natCast_eq_zero_iff] at ha
  obtain ⟨q, hq⟩ := ha
  refine ⟨(q : ZMod (2 ^ m)), ?_⟩
  rw [← ZMod.natCast_zmod_val a, hq]
  push_cast; rfl

/-! ## Certificates -/

/-- Chain value mod `2^(3s)`. -/
abbrev v3 (s : ℕ) (C : Finset (ℕ × ℕ)) : ZMod (2 ^ (3 * s)) := cval (inv7 (3 * s)) C

/-- `lift x u = x + 2^(2s) u` in `ZMod (2^(3s))`. -/
def lift (s : ℕ) (x : ZMod (2 ^ (2 * s))) (u : ZMod (2 ^ s)) : ZMod (2 ^ (3 * s)) :=
  ((x.val + 2 ^ (2 * s) * u.val : ℕ) : ZMod (2 ^ (3 * s)))

/-- Next state: `7^h ((z - v(C)) / 2^s) mod 2^(2s)`. -/
def nxt (s : ℕ) (C : Finset (ℕ × ℕ)) (h : ℕ) (z : ZMod (2 ^ (3 * s))) : ZMod (2 ^ (2 * s)) :=
  ((7 ^ h * ((z - v3 s C).val / 2 ^ s) : ℕ) : ZMod (2 ^ (2 * s)))

/-- A two-block look-ahead potential certificate for `(7,2)` with block size `s`,
heights `≤ H`: a policy (chain + height for each 3-block window), a potential `V` on
states (2-block windows), and a drift bound `g`. This is what `verify.c` checks. -/
structure Cert (s H : ℕ) where
  ch : ZMod (2 ^ (3 * s)) → Finset (ℕ × ℕ)
  hgt : ZMod (2 ^ (3 * s)) → ℕ
  V : ZMod (2 ^ (2 * s)) → ℝ
  g : ℝ
  chain : ∀ z, ∀ a ∈ ch z, ∀ b ∈ ch z, a.1 < b.1 → a.2 < b.2
  inj : ∀ z, ∀ a ∈ ch z, ∀ b ∈ ch z, a.1 = b.1 → a = b
  alpha_lt : ∀ z, ∀ a ∈ ch z, a.1 < s
  gamma_lt : ∀ z, ∀ a ∈ ch z, a.2 < hgt z
  hgt_le : ∀ z, hgt z ≤ H
  res : ∀ z, 2 ^ s ∣ (z - v3 s (ch z)).val
  drift : ∀ x : ZMod (2 ^ (2 * s)),
    ∑ u : ZMod (2 ^ s), ((hgt (lift s x u) : ℝ) + V (nxt s (ch (lift s x u)) (hgt (lift s x u)) (lift s x u)))
      ≤ 2 ^ s * (V x + g)

/-! ## The encoding process -/

noncomputable section process
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ}

/-- The 3-block window read at step `t`. -/
def zAt (s : ℕ) (t G : ℕ) (ρ : ZMod (2 ^ m)) : ZMod (2 ^ (3 * s)) :=
  win (s * t) (3 * s) ((7 : ZMod (2 ^ m)) ^ G * ρ)

def step (t : ℕ) (p : ℕ × ZMod (2 ^ m)) : ℕ × ZMod (2 ^ m) :=
  (max (p.1 + K.hgt (zAt s t p.1 p.2)) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊,
   p.2 - 2 ^ (s * t) * inv7 m ^ p.1 * cval (inv7 m) (K.ch (zAt s t p.1 p.2)))

def proc (y : ZMod (2 ^ m)) : ℕ → ℕ × ZMod (2 ^ m)
  | 0 => (0, y)
  | t + 1 => step K lam t (proc y t)

variable (y : ZMod (2 ^ m))

abbrev GG (t : ℕ) : ℕ := (proc K lam y t).1
abbrev RR (t : ℕ) : ZMod (2 ^ m) := (proc K lam y t).2
abbrev WW (t : ℕ) : ZMod (2 ^ m) := (7 : ZMod (2 ^ m)) ^ GG K lam y t * RR K lam y t
abbrev ZZ (t : ℕ) : ZMod (2 ^ (3 * s)) := win (s * t) (3 * s) (WW K lam y t)
/-- The state (2-block window) at step `t`. -/
abbrev XX (t : ℕ) : ZMod (2 ^ (2 * s)) := win (s * t) (2 * s) (WW K lam y t)
abbrev CC (t : ℕ) : Finset (ℕ × ℕ) := K.ch (ZZ K lam y t)
abbrev hh (t : ℕ) : ℕ := K.hgt (ZZ K lam y t)

lemma GG_succ (t : ℕ) : GG K lam y (t + 1) = max (GG K lam y t + hh K lam y t) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ := rfl

lemma RR_succ (t : ℕ) : RR K lam y (t + 1) =
    RR K lam y t - 2 ^ (s * t) * inv7 m ^ GG K lam y t * cval (inv7 m) (CC K lam y t) := rfl

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

/-- Telescoping: `y = Σ_{j<t} 2^{sj} 7^{-G_j} v(C_j) + ρ_t`. -/
lemma y_eq_sum (t : ℕ) : y = (∑ j ∈ range t, 2 ^ (s * j) * inv7 m ^ GG K lam y j * cval (inv7 m) (CC K lam y j))
    + RR K lam y t := by
  induction t with
  | zero => simp [RR, proc]
  | succ t ih => rw [sum_range_succ, RR_succ]; linear_combination ih

/-- `ρ_t` is divisible by `2^{st}` for `t ≤ N`. -/
lemma RR_dvd {N : ℕ} (hm : m = s * N) (t : ℕ) (ht : t ≤ N) : ∃ r, RR K lam y t = 2 ^ (s * t) * r := by
  induction t with
  | zero => exact ⟨y, by simp [RR, proc]⟩
  | succ t ih =>
    obtain ⟨r, hr⟩ := ih (by omega)
    have hst : s * t + s ≤ m := by rw [hm]; nlinarith
    set G := GG K lam y t
    set C := CC K lam y t
    -- residue: 7^G r ≡ v(C) mod 2^s
    have hres := K.res (ZZ K lam y t)
    rw [← ZMod.natCast_eq_zero_iff, val_cast_eq_castHom (m := 3 * s) (j := s) (by omega), map_sub] at hres
    have hv : red s (by omega : s ≤ 3 * s) (v3 s C) = cval (inv7 s) C := red_cval _ _
    have hz : red s (by omega) (ZZ K lam y t) = red s (by omega : s ≤ m) ((7 : ZMod (2 ^ m)) ^ G * r) := by
      show red s _ (win (s * t) (3 * s) _) = _
      rw [win_red (by omega)]
      show win (s * t) s ((7 : ZMod (2 ^ m)) ^ G * RR K lam y t) = _
      rw [hr, mul_left_comm, win_two_pow_mul (by omega), val_cast_eq_castHom (by omega)]
    rw [hz, hv] at hres
    have h0 : red s (by omega : s ≤ m) ((7 : ZMod (2 ^ m)) ^ G * r - cval (inv7 m) C) = 0 := by
      rw [map_sub, red_cval]; exact hres
    obtain ⟨e, he⟩ := exists_eq_two_pow_mul _ _ h0
    refine ⟨inv7 m ^ G * e, ?_⟩
    rw [RR_succ, hr]
    have : r - inv7 m ^ G * cval (inv7 m) C = inv7 m ^ G * (7 ^ G * r - cval (inv7 m) C) := by
      linear_combination (-r) * pow7_mul_inv7 m G
    rw [mul_add s t 1, mul_one, pow_add, show (2:ZMod (2^m)) ^ (s * t) * r - 2 ^ (s * t) * inv7 m ^ G * cval (inv7 m) C
      = 2 ^ (s * t) * (r - inv7 m ^ G * cval (inv7 m) C) by ring, this, he]
    ring

lemma RR_N {N : ℕ} (hm : m = s * N) : RR K lam y N = 0 := by
  obtain ⟨r, hr⟩ := RR_dvd K lam y hm N le_rfl
  rw [hr, ← hm]
  have : ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 0 := ZMod.natCast_self _
  push_cast at this
  rw [this, zero_mul]

end process


/-! ## The integer `n(y)`: congruence, injectivity, representability -/

lemma pow_two_seven_dvd {a b c d : ℕ} (h : 2 ^ a * 7 ^ b ∣ 2 ^ c * 7 ^ d) : a ≤ c ∧ b ≤ d := by
  constructor
  · have h1 : 2 ^ a ∣ 2 ^ c * 7 ^ d := dvd_trans (dvd_mul_right _ _) h
    have hc : Nat.Coprime (2 ^ a) (7 ^ d) := Nat.Coprime.pow _ _ (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hc.dvd_of_dvd_mul_right h1)
  · have h1 : 7 ^ b ∣ 2 ^ c * 7 ^ d := dvd_trans (dvd_mul_left _ _) h
    have hc : Nat.Coprime (7 ^ b) (2 ^ c) := Nat.Coprime.pow _ _ (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hc.dvd_of_dvd_mul_left h1)

lemma seven_pow_sub {m A k : ℕ} (h : k ≤ A) :
    (7 : ZMod (2 ^ m)) ^ (A - k) = 7 ^ A * inv7 m ^ k := by
  have : (7 : ZMod (2 ^ m)) ^ A = 7 ^ (A - k) * 7 ^ k := by rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc, pow7_mul_inv7, mul_one]

noncomputable section encoding
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ} (y : ZMod (2 ^ m))

/-- The index set of summands. -/
def idx (N : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) := (range N).sigma (fun t => CC K lam y t)

/-- Exponent pair of a summand: `(2-exponent, 7-exponent)`. -/
def ex1 (i : Σ _ : ℕ, ℕ × ℕ) : ℕ := s * i.1 + i.2.1
def ex2 (A : ℕ) (i : Σ _ : ℕ, ℕ × ℕ) : ℕ := A - GG K lam y i.1 - i.2.2

/-- The encoded integer. -/
def nval (A N : ℕ) : ℕ := ∑ i ∈ idx K lam y N, 2 ^ ex1 (s := s) i * 7 ^ ex2 K lam y A i

lemma gamma_add_lt {N A t : ℕ} (hA : GG K lam y N ≤ A) (ht : t < N) {a : ℕ × ℕ} (ha : a ∈ CC K lam y t) :
    GG K lam y t + a.2 < GG K lam y (t + 1) ∧ GG K lam y (t + 1) ≤ A :=
  ⟨lt_of_lt_of_le (Nat.add_lt_add_left (K.gamma_lt _ a ha) _) (GG_le_succ K lam y t),
   le_trans (GG_mono K lam y (by omega)) hA⟩

/-- Distinct summands have strictly anti-ordered exponent pairs. -/
lemma anti {N A : ℕ} (hA : GG K lam y N ≤ A) {i j : Σ _ : ℕ, ℕ × ℕ}
    (hi : i ∈ idx K lam y N) (hj : j ∈ idx K lam y N) (hlt : i.1 < j.1 ∨ (i.1 = j.1 ∧ i.2.1 < j.2.1)) :
    ex1 (s := s) i < ex1 (s := s) j ∧ ex2 K lam y A j < ex2 K lam y A i := by
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

lemma nval_representable {N A : ℕ} (hA : GG K lam y N ≤ A) : Representable 7 2 (nval K lam y A N) := by
  set f : (Σ _ : ℕ, ℕ × ℕ) → ℕ := fun i => 2 ^ ex1 (s := s) i * 7 ^ ex2 K lam y A i with hf
  -- distinct summands: incomparable
  have key : ∀ i ∈ idx K lam y N, ∀ j ∈ idx K lam y N, i ≠ j → ¬ f i ∣ f j := by
    intro i hi j hj hne hdvd
    have hd := pow_two_seven_dvd hdvd
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
    exact ⟨ex2 K lam y A i, ex1 (s := s) i, by rw [hf, mul_comm]⟩
  · intro x hx x' hx' hne
    simp only [coe_image, Set.mem_image, mem_coe] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hx'
    exact key i hi j hj (fun h => hne (h ▸ rfl))
  · rw [sum_image (fun i hi j hj h => hinj hi hj h)]
    rfl

/-- `n(y) ≡ 7^A y (mod 2^{sN})` for admissible `y`. -/
lemma nval_cast {N A : ℕ} (hm : m = s * N) (hA : GG K lam y N ≤ A) :
    ((nval K lam y A N : ℕ) : ZMod (2 ^ m)) = 7 ^ A * y := by
  have hy := y_eq_sum K lam y N
  rw [RR_N K lam y hm, add_zero] at hy
  conv_rhs => rw [hy]
  rw [nval, idx, sum_sigma, Nat.cast_sum, mul_sum]
  refine sum_congr rfl (fun t ht => ?_)
  rw [Nat.cast_sum, cval, mul_sum, mul_sum]
  refine sum_congr rfl (fun a ha => ?_)
  have hle := gamma_add_lt K lam y hA (mem_range.mp ht) ha
  unfold ex1 ex2
  push_cast
  rw [Nat.sub_sub, seven_pow_sub (by omega), pow_add, pow_add]
  ring

lemma nval_inj {N A : ℕ} (hm : m = s * N) {y y' : ZMod (2 ^ m)} (hA : GG K lam y N ≤ A)
    (hA' : GG K lam y' N ≤ A) (h : nval K lam y A N = nval K lam y' A N) : y = y' := by
  have h1 := nval_cast K lam y hm hA
  have h2 := nval_cast K lam y' hm hA'
  rw [h, h2] at h1
  calc y = (7 ^ A * inv7 m ^ A) * y := by rw [pow7_mul_inv7, one_mul]
    _ = inv7 m ^ A * (7 ^ A * y) := by ring
    _ = inv7 m ^ A * (7 ^ A * y') := by rw [h1]
    _ = (7 ^ A * inv7 m ^ A) * y' := by ring
    _ = y' := by rw [pow7_mul_inv7, one_mul]

end encoding


/-! ## Size bound -/

lemma geom_two_lt (s : ℕ) : ∑ x ∈ range s, 2 ^ x < 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [sum_range_succ, pow_succ]; omega

lemma sum_fst_lt {s H : ℕ} (K : Cert s H) (z : ZMod (2 ^ (3 * s))) : ∑ a ∈ K.ch z, 2 ^ a.1 < 2 ^ s := by
  have hinj : Set.InjOn Prod.fst (K.ch z : Set (ℕ × ℕ)) := fun a ha b hb h => K.inj z a ha b hb h
  rw [← sum_image (f := fun x => 2 ^ x) (fun a ha b hb h => hinj ha hb h)]
  refine lt_of_le_of_lt (sum_le_sum_of_subset (fun x hx => ?_)) (geom_two_lt s)
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
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ} (y : ZMod (2 ^ m))

lemma nval_le_nat (A N : ℕ) :
    nval K lam y A N ≤ ∑ t ∈ range N, 2 ^ s * 2 ^ (s * t) * 7 ^ (A - GG K lam y t) := by
  rw [nval, idx, sum_sigma]
  refine sum_le_sum (fun t _ => ?_)
  calc ∑ a ∈ CC K lam y t, 2 ^ ex1 (s := s) ⟨t, a⟩ * 7 ^ ex2 K lam y A ⟨t, a⟩
      ≤ ∑ a ∈ CC K lam y t, 2 ^ (s * t) * 7 ^ (A - GG K lam y t) * 2 ^ a.1 := by
        refine sum_le_sum (fun a _ => ?_)
        unfold ex1 ex2
        rw [pow_add]
        have : 7 ^ (A - GG K lam y t - a.2) ≤ 7 ^ (A - GG K lam y t) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
        calc 2 ^ (s * t) * 2 ^ a.1 * 7 ^ (A - GG K lam y t - a.2)
            ≤ 2 ^ (s * t) * 2 ^ a.1 * 7 ^ (A - GG K lam y t) := Nat.mul_le_mul_left _ this
          _ = _ := by ring
    _ = 2 ^ (s * t) * 7 ^ (A - GG K lam y t) * ∑ a ∈ CC K lam y t, 2 ^ a.1 := by rw [mul_sum]
    _ ≤ 2 ^ (s * t) * 7 ^ (A - GG K lam y t) * 2 ^ s := Nat.mul_le_mul_left _ (sum_fst_lt K _).le
    _ = _ := by ring

lemma seven_pow_GG_ge (t : ℕ) : ((7 : ℝ) ^ lam) ^ t ≤ (7 : ℝ) ^ GG K lam y t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := ceil_le_GG K lam y t
  have h2 := Nat.le_ceil ((t : ℝ) * lam)
  have h3 : ((⌈(t : ℝ) * lam⌉₊ : ℕ) : ℝ) ≤ (GG K lam y t : ℝ) := by exact_mod_cast this
  linarith

/-- `n(y) ≤ 2^s 7^D (2^s)^N ℓ / (2^s - ℓ)` with `ℓ = 7^λ`, for admissible `y`. -/
lemma nval_le_real {N A : ℕ} (hA : GG K lam y N ≤ A) (hlam : (7 : ℝ) ^ lam < 2 ^ s) (D : ℝ)
    (hAD : (A : ℝ) ≤ N * lam + D) :
    (nval K lam y A N : ℝ) ≤ 2 ^ s * 7 ^ D * ((2 ^ s) ^ N * 7 ^ lam / (2 ^ s - 7 ^ lam)) := by
  set ℓ : ℝ := (7 : ℝ) ^ lam with hℓ
  have hℓ0 : 0 < ℓ := Real.rpow_pos_of_pos (by norm_num) _
  have h7A : (7 : ℝ) ^ A ≤ 7 ^ D * ℓ ^ N := by
    rw [← Real.rpow_natCast, hℓ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hterm : ∀ t ∈ range N, (7 : ℝ) ^ (A - GG K lam y t) ≤ 7 ^ D * ℓ ^ (N - t) := by
    intro t ht
    have htN := mem_range.mp ht
    have hGA : GG K lam y t ≤ A := le_trans (GG_mono K lam y htN.le) hA
    have h7G : (0 : ℝ) < 7 ^ GG K lam y t := by positivity
    refine le_of_mul_le_mul_right ?_ h7G
    rw [← pow_add, Nat.sub_add_cancel hGA]
    calc (7 : ℝ) ^ A ≤ 7 ^ D * ℓ ^ N := h7A
      _ = 7 ^ D * ℓ ^ (N - t) * ℓ ^ t := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel htN.le]
      _ ≤ 7 ^ D * ℓ ^ (N - t) * 7 ^ GG K lam y t := by
          gcongr
          exact seven_pow_GG_ge K lam y t
  have h1 : (nval K lam y A N : ℝ) ≤ ∑ t ∈ range N, 2 ^ s * 2 ^ (s * t) * (7 : ℝ) ^ (A - GG K lam y t) := by
    exact_mod_cast nval_le_nat K lam y A N
  refine h1.trans ?_
  calc ∑ t ∈ range N, 2 ^ s * 2 ^ (s * t) * (7 : ℝ) ^ (A - GG K lam y t)
      ≤ ∑ t ∈ range N, 2 ^ s * 7 ^ D * ((2 ^ s) ^ t * ℓ ^ (N - t)) := by
        refine sum_le_sum (fun t ht => ?_)
        rw [pow_mul]
        have := hterm t ht
        have : (0 : ℝ) ≤ 2 ^ s * (2 ^ s) ^ t := by positivity
        nlinarith
    _ = 2 ^ s * 7 ^ D * ∑ t ∈ range N, (2 ^ s) ^ t * ℓ ^ (N - t) := by rw [mul_sum]
    _ ≤ _ := by
        gcongr
        exact geom_aux ℓ (2 ^ s) hℓ0.le hlam N

end sizes


/-! ## One step of the state: the transition -/

lemma val_val_cast {m j j' : ℕ} (h : j' ≤ j) (x : ZMod (2 ^ m)) :
    (((x.val : ZMod (2 ^ j)).val : ℕ) : ZMod (2 ^ j')) = (x.val : ZMod (2 ^ j')) := by
  rw [ZMod.val_natCast, natCast_mod_pow h]

lemma nxt_eq (s : ℕ) (C : Finset (ℕ × ℕ)) (h : ℕ) (z : ZMod (2 ^ (3 * s))) :
    nxt s C h z = 7 ^ h * win s (2 * s) (z - v3 s C) := by
  unfold nxt win; push_cast; rfl

noncomputable section transition
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ} (y : ZMod (2 ^ m))

/-- On an unpadded step, the next state is `nxt` of the current 3-block window. -/
lemma XX_succ {N : ℕ} (hm : m = s * N) (t : ℕ) (ht : t + 3 ≤ N)
    (hpad : GG K lam y (t + 1) = GG K lam y t + hh K lam y t) :
    XX K lam y (t + 1) = nxt s (CC K lam y t) (hh K lam y t) (ZZ K lam y t) := by
  obtain ⟨r', hr'⟩ := RR_dvd K lam y hm (t + 1) (by omega)
  have hk : s * t + 3 * s ≤ m := by rw [hm]; nlinarith
  have hk' : s * (t + 1) + 2 * s ≤ m := by rw [mul_add, mul_one]; omega
  have e1 := RR_succ K lam y t
  rw [hr'] at e1
  have hw : WW K lam y t + 2 ^ (s * t) * (-cval (inv7 m) (CC K lam y t)) =
      2 ^ (s * t) * (2 ^ s * (7 ^ GG K lam y t * r')) := by
    show (7 : ZMod (2 ^ m)) ^ GG K lam y t * RR K lam y t + _ = _
    linear_combination (-(7 : ZMod (2 ^ m)) ^ GG K lam y t) * e1 +
      (2 ^ (s * t) * cval (inv7 m) (CC K lam y t)) * pow7_mul_inv7 m (GG K lam y t)
  have hz : ZZ K lam y t - v3 s (CC K lam y t) =
      2 ^ s * (((7 : ZMod (2 ^ m)) ^ GG K lam y t * r').val : ZMod (2 ^ (3 * s))) := by
    have h1 := win_add (k := s * t) (j := 3 * s) (by omega) (WW K lam y t) (-cval (inv7 m) (CC K lam y t))
    rw [hw, win_two_pow_mul (by omega)] at h1
    rw [val_cast_eq_castHom (m := m) (j := 3 * s) (by omega), val_cast_eq_castHom (m := m) (j := 3 * s) (by omega),
      map_neg, map_mul, map_pow, map_ofNat, red_cval (m := m) (j := 3 * s) (by omega)] at h1
    rw [val_cast_eq_castHom (m := m) (j := 3 * s) (by omega)]
    linear_combination -h1
  rw [nxt_eq, hz, win_two_pow_mul (m := 3 * s) (by omega), val_val_cast (by omega)]
  show win (s * (t + 1)) (2 * s) ((7 : ZMod (2 ^ m)) ^ GG K lam y (t + 1) * RR K lam y (t + 1)) = _
  rw [hr', hpad, mul_left_comm, win_two_pow_mul hk', val_cast_eq_castHom (m := m) (j := 2 * s) (by omega),
    val_cast_eq_castHom (m := m) (j := 2 * s) (by omega), map_mul, map_mul, map_pow, map_pow, map_ofNat, pow_add]
  ring

end transition


/-! ## Fresh look-ahead: locality, fibers, averaging -/

lemma lift_eq (s : ℕ) (z : ZMod (2 ^ (3 * s))) (E : ℕ) :
    z + 2 ^ (2 * s) * (E : ZMod (2 ^ (3 * s))) =
      lift s (z.val : ZMod (2 ^ (2 * s))) (((z.val / 2 ^ (2 * s) + E : ℕ) : ZMod (2 ^ s))) := by
  have hL : ((z.val + 2 ^ (2 * s) * E : ℕ) : ZMod (2 ^ (3 * s))) = z + 2 ^ (2 * s) * (E : ZMod (2 ^ (3 * s))) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [← hL, lift, ZMod.val_natCast, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff']
  set a := z.val
  set q := a / 2 ^ (2 * s) + E
  have h1 : a + 2 ^ (2 * s) * E = (a % 2 ^ (2 * s) + 2 ^ (2 * s) * (q % 2 ^ s)) + 2 ^ (3 * s) * (q / 2 ^ s) := by
    calc a + 2 ^ (2 * s) * E = a % 2 ^ (2 * s) + 2 ^ (2 * s) * (a / 2 ^ (2 * s)) + 2 ^ (2 * s) * E := by
          rw [Nat.mod_add_div]
      _ = a % 2 ^ (2 * s) + 2 ^ (2 * s) * q := by ring
      _ = a % 2 ^ (2 * s) + 2 ^ (2 * s) * (q % 2 ^ s + 2 ^ s * (q / 2 ^ s)) := by rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [h1, Nat.add_mul_mod_self_left]

lemma fiber (s : ℕ) (F : ZMod (2 ^ (3 * s)) → ℝ) (z : ZMod (2 ^ (3 * s))) (c : ZMod (2 ^ s)) (hc : IsUnit c)
    (e : ZMod (2 ^ s) → ℕ) (he : ∀ δ, ((e δ : ℕ) : ZMod (2 ^ s)) = c * δ) :
    ∑ δ : ZMod (2 ^ s), F (z + 2 ^ (2 * s) * (e δ : ZMod (2 ^ (3 * s)))) =
      ∑ u : ZMod (2 ^ s), F (lift s (z.val : ZMod (2 ^ (2 * s))) u) := by
  refine Fintype.sum_equiv ((Units.mulLeft hc.unit).trans (Equiv.addLeft ((z.val / 2 ^ (2 * s) : ℕ) : ZMod (2 ^ s))))
    _ _ (fun δ => ?_)
  rw [lift_eq]
  congr 2
  push_cast
  rw [he]
  rfl

lemma isUnit_seven_pow (s G : ℕ) : IsUnit ((7 : ZMod (2 ^ s)) ^ G) :=
  (IsUnit.of_mul_eq_one _ (seven_mul_inv7 s)).pow G

noncomputable section fresh
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ}

lemma XX_eq_ZZ (y : ZMod (2 ^ m)) (t : ℕ) : XX K lam y t = ((ZZ K lam y t).val : ZMod (2 ^ (2 * s))) := by
  show win (s * t) (2 * s) _ = _
  rw [win, ZZ, win, ZMod.val_natCast, natCast_mod_pow (by omega)]

/-- Shifting `y` by a multiple of `2^{s(t+2)}` does not change the first `t` steps. -/
lemma local_shift {N : ℕ} (hm : m = s * N) (y δ : ZMod (2 ^ m)) (t : ℕ) (ht : t + 2 ≤ N) :
    ∀ j ≤ t, GG K lam (y + 2 ^ (s * (t + 2)) * δ) j = GG K lam y j ∧
      RR K lam (y + 2 ^ (s * (t + 2)) * δ) j = RR K lam y j + 2 ^ (s * (t + 2)) * δ := by
  have hK : s * (t + 2) ≤ m := by rw [hm]; exact Nat.mul_le_mul_left s ht
  intro j hj
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hG, hR⟩ := ih (by omega)
    have hjk : s * j + 3 * s ≤ s * (t + 2) := by
      have := Nat.mul_le_mul_left s (show j + 3 ≤ t + 2 by omega)
      rw [mul_add] at this; omega
    have hZ : ZZ K lam (y + 2 ^ (s * (t + 2)) * δ) j = ZZ K lam y j := by
      show win (s * j) (3 * s) ((7 : ZMod (2 ^ m)) ^ GG K lam _ j * RR K lam _ j) =
        win (s * j) (3 * s) ((7 : ZMod (2 ^ m)) ^ GG K lam y j * RR K lam y j)
      rw [hG, hR, mul_add, mul_left_comm, win_add_high hjk hK]
    refine ⟨?_, ?_⟩
    · rw [GG_succ, GG_succ, hG, hh, hh, hZ]
    · rw [RR_succ, RR_succ, hR, hG, CC, CC, hZ]; ring

/-- At step `t` the shift moves the look-ahead digit only. -/
lemma ZZ_shift {N : ℕ} (hm : m = s * N) (y δ : ZMod (2 ^ m)) (t : ℕ) (ht : t + 3 ≤ N) :
    GG K lam (y + 2 ^ (s * (t + 2)) * δ) t = GG K lam y t ∧
    XX K lam (y + 2 ^ (s * (t + 2)) * δ) t = XX K lam y t ∧
    ZZ K lam (y + 2 ^ (s * (t + 2)) * δ) t =
      ZZ K lam y t + 2 ^ (2 * s) * ((((7 : ZMod (2 ^ m)) ^ GG K lam y t * δ).val : ℕ) : ZMod (2 ^ (3 * s))) := by
  obtain ⟨hG, hR⟩ := local_shift K lam hm y δ t (by omega) t le_rfl
  have hk : s * t + 3 * s ≤ m := by
    rw [hm]; have := Nat.mul_le_mul_left s ht; rw [mul_add] at this; linarith
  have hK : s * (t + 2) ≤ m := by rw [hm]; exact Nat.mul_le_mul_left s (by omega)
  have hk2 : s * t + 2 * s ≤ s * (t + 2) := by rw [mul_add]; omega
  refine ⟨hG, ?_, ?_⟩
  · show win (s * t) (2 * s) ((7 : ZMod (2 ^ m)) ^ GG K lam _ t * RR K lam _ t) =
      win (s * t) (2 * s) ((7 : ZMod (2 ^ m)) ^ GG K lam y t * RR K lam y t)
    rw [hG, hR, mul_add, mul_left_comm, win_add_high hk2 hK]
  show win (s * t) (3 * s) ((7 : ZMod (2 ^ m)) ^ GG K lam _ t * RR K lam _ t) = _
  have e : (7 : ZMod (2 ^ m)) ^ GG K lam y t * (RR K lam y t + 2 ^ (s * (t + 2)) * δ) =
      WW K lam y t + 2 ^ (s * t) * (2 ^ (2 * s) * ((7 : ZMod (2 ^ m)) ^ GG K lam y t * δ)) := by
    show _ = (7 : ZMod (2 ^ m)) ^ GG K lam y t * RR K lam y t + _
    rw [show s * (t + 2) = s * t + 2 * s by ring, pow_add]; ring
  rw [hG, hR, e, win_add (by omega), val_cast_eq_castHom (m := m) (j := 3 * s) (by omega),
    val_cast_eq_castHom (m := m) (j := 3 * s) (by omega), map_mul, map_pow, map_ofNat]

/-- Averaging over the fresh block: the look-ahead digit is uniform given the past. -/
lemma average {N : ℕ} (hm : m = s * N) (t : ℕ) (ht : t + 3 ≤ N)
    (φ : ℕ → ZMod (2 ^ (2 * s)) → ℝ) (F : ZMod (2 ^ (3 * s)) → ℝ) :
    (2 ^ s : ℝ) * ∑ y : ZMod (2 ^ m), φ (GG K lam y t) (XX K lam y t) * F (ZZ K lam y t) =
      ∑ y : ZMod (2 ^ m), φ (GG K lam y t) (XX K lam y t) * ∑ u : ZMod (2 ^ s), F (lift s (XX K lam y t) u) := by
  have hsm : s ≤ m := by
    rw [hm]; have := Nat.mul_le_mul_left s (show 1 ≤ N by omega); linarith
  set T : ZMod (2 ^ s) → ZMod (2 ^ m) := fun δ => 2 ^ (s * (t + 2)) * ((δ.val : ℕ) : ZMod (2 ^ m)) with hT
  have hcard : (2 ^ s : ℝ) = ∑ _δ : ZMod (2 ^ s), (1 : ℝ) := by simp [ZMod.card]
  rw [hcard, sum_mul, one_mul]
  have step1 : ∀ δ : ZMod (2 ^ s),
      ∑ y : ZMod (2 ^ m), φ (GG K lam y t) (XX K lam y t) * F (ZZ K lam y t) =
      ∑ y : ZMod (2 ^ m), φ (GG K lam y t) (XX K lam y t) *
        F (ZZ K lam y t + 2 ^ (2 * s) *
          ((((7 : ZMod (2 ^ m)) ^ GG K lam y t * ((δ.val : ℕ) : ZMod (2 ^ m))).val : ℕ) : ZMod (2 ^ (3 * s)))) := by
    intro δ
    refine (Fintype.sum_equiv (Equiv.addRight (2 ^ (s * (t + 2)) * ((δ.val : ℕ) : ZMod (2 ^ m)))) _ _
      (fun y => ?_)).symm
    obtain ⟨hG, hX, hZ⟩ := ZZ_shift K lam hm y ((δ.val : ℕ) : ZMod (2 ^ m)) t ht
    simp only [Equiv.coe_addRight]
    rw [hG, hX, hZ]
  rw [sum_congr rfl (fun δ _ => step1 δ), sum_comm]
  refine sum_congr rfl (fun y _ => ?_)
  rw [← mul_sum, XX_eq_ZZ K lam y t]
  congr 1
  refine fiber s F (ZZ K lam y t) _ (isUnit_seven_pow s (GG K lam y t)) _ (fun δ => ?_)
  rw [val_cast_eq_castHom hsm, map_mul, map_pow, map_ofNat, ← val_cast_eq_castHom hsm, ZMod.val_natCast,
    natCast_mod_pow hsm, ZMod.natCast_zmod_val]

end fresh


/-! ## The exponential potential -/

lemma exp_le_quad {w : ℝ} (hw : |w| ≤ 1) : Real.exp w ≤ 1 + w + w ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hw
  have h2 := le_abs_self (Real.exp w - 1 - w)
  linarith

/-- Next-state value as a function of the 3-block window. -/
noncomputable abbrev Fz {s H : ℕ} (K : Cert s H) (lam θ : ℝ) (z : ZMod (2 ^ (3 * s))) : ℝ :=
  Real.exp (θ * ((K.hgt z : ℝ) + K.V (nxt s (K.ch z) (K.hgt z) z) - lam))

/-- The certificate drift, exponentiated. -/
lemma drift_exp {s H : ℕ} (K : Cert s H) (lam θ B : ℝ) (hB : ∀ x, |K.V x| ≤ B) (hθ : 0 ≤ θ)
    (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1) (x : ZMod (2 ^ (2 * s))) :
    ∑ u : ZMod (2 ^ s), Fz K lam θ (lift s x u) ≤
      2 ^ s * Real.exp (θ * (K.V x + K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) := by
  set R : ℝ := (H : ℝ) + 2 * B + |K.g| with hR
  set a : ZMod (2 ^ s) → ℝ := fun u => (K.hgt (lift s x u) : ℝ) +
    K.V (nxt s (K.ch (lift s x u)) (K.hgt (lift s x u)) (lift s x u)) with ha
  set C : ℝ := θ * (K.V x + K.g - lam) with hC
  have hW : ∀ u, |a u - K.V x - K.g| ≤ R := by
    intro u
    have h1 := abs_le.mp (hB (nxt s (K.ch (lift s x u)) (K.hgt (lift s x u)) (lift s x u)))
    have h2 := abs_le.mp (hB x)
    have h3 : (K.hgt (lift s x u) : ℝ) ≤ H := by exact_mod_cast K.hgt_le _
    have h4 : (0 : ℝ) ≤ K.hgt (lift s x u) := Nat.cast_nonneg _
    have h5 := le_abs_self K.g
    have h6 := neg_abs_le K.g
    rw [abs_le]; simp only [ha]; constructor <;> linarith
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hW 0)
  have key : ∀ u, Fz K lam θ (lift s x u) ≤
      Real.exp C * (1 + θ * (a u - K.V x - K.g) + θ ^ 2 * R ^ 2) := by
    intro u
    have e : Fz K lam θ (lift s x u) = Real.exp C * Real.exp (θ * (a u - K.V x - K.g)) := by
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
  have hsum : ∑ u : ZMod (2 ^ s), a u ≤ 2 ^ s * (K.V x + K.g) := K.drift x
  have hcard : ∑ _u : ZMod (2 ^ s), (1 : ℝ) = 2 ^ s := by simp [ZMod.card]
  calc ∑ u : ZMod (2 ^ s), Fz K lam θ (lift s x u)
      ≤ ∑ u : ZMod (2 ^ s), Real.exp C * (1 + θ * (a u - K.V x - K.g) + θ ^ 2 * R ^ 2) := sum_le_sum (fun u _ => key u)
    _ = Real.exp C * (2 ^ s * (1 + θ ^ 2 * R ^ 2) + θ * (∑ u : ZMod (2 ^ s), a u - 2 ^ s * (K.V x + K.g))) := by
        rw [← mul_sum]; congr 1
        simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        push_cast; ring
    _ ≤ Real.exp C * (2 ^ s * (1 + θ ^ 2 * R ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : θ * (∑ u : ZMod (2 ^ s), a u - 2 ^ s * (K.V x + K.g)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hθ (by linarith)
        linarith
    _ ≤ Real.exp C * (2 ^ s * Real.exp (θ ^ 2 * R ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := Real.add_one_le_exp (θ ^ 2 * R ^ 2); linarith
    _ = _ := by rw [Real.exp_add]; ring

noncomputable section potential
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ}

/-- The potential `Ψ_t = exp(θ (G_t - tλ + V(X_t)))`. -/
def Psi (θ : ℝ) (y : ZMod (2 ^ m)) (t : ℕ) : ℝ :=
  Real.exp (θ * ((GG K lam y t : ℝ) - t * lam + K.V (XX K lam y t)))

lemma Psi_step {N : ℕ} (hm : m = s * N) (hlam : 0 ≤ lam) (θ B : ℝ) (hθ : 0 ≤ θ) (hB : ∀ x, |K.V x| ≤ B)
    (y : ZMod (2 ^ m)) (t : ℕ) (ht : t + 3 ≤ N) :
    Psi K lam θ y (t + 1) ≤
      Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t) + Real.exp (θ * (1 + B)) := by
  rcases max_choice (GG K lam y t + hh K lam y t) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ with h | h
  · -- unpadded
    have hpad : GG K lam y (t + 1) = GG K lam y t + hh K lam y t := by rw [GG_succ, h]
    have hX := XX_succ K lam y hm t ht hpad
    have e : Psi K lam θ y (t + 1) =
        Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t) := by
      rw [Psi, hX, hpad, Fz, ← Real.exp_add]; congr 1; push_cast; ring
    rw [e]; linarith [Real.exp_pos (θ * (1 + B))]
  · -- padded
    have hG : GG K lam y (t + 1) = ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ := by rw [GG_succ, h]
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

lemma Psi_sum_step {N : ℕ} (hm : m = s * N) (hlam : 0 ≤ lam) (θ B : ℝ) (hθ : 0 ≤ θ) (hB : ∀ x, |K.V x| ≤ B)
    (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1) (t : ℕ) (ht : t + 3 ≤ N) :
    ∑ y : ZMod (2 ^ m), Psi K lam θ y (t + 1) ≤
      Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) * ∑ y : ZMod (2 ^ m), Psi K lam θ y t
        + 2 ^ m * Real.exp (θ * (1 + B)) := by
  set ρ := Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2)
  have h1 : ∑ y : ZMod (2 ^ m), Psi K lam θ y (t + 1) ≤
      ∑ y : ZMod (2 ^ m), Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t)
        + 2 ^ m * Real.exp (θ * (1 + B)) := by
    have := sum_le_sum (fun y (_ : y ∈ univ) => Psi_step K lam hm hlam θ B hθ hB y t ht)
    rw [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul] at this
    push_cast at this; exact this
  have h2 := average K lam hm t ht (fun G _ => Real.exp (θ * ((G : ℝ) - t * lam))) (Fz K lam θ)
  have h3 : (2 ^ s : ℝ) * ∑ y : ZMod (2 ^ m), Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * Fz K lam θ (ZZ K lam y t)
      ≤ 2 ^ s * (ρ * ∑ y : ZMod (2 ^ m), Psi K lam θ y t) := by
    rw [h2, mul_sum, mul_sum]
    refine sum_le_sum (fun y _ => ?_)
    have hd := drift_exp K lam θ B hB hθ hθR (XX K lam y t)
    calc Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) * ∑ u : ZMod (2 ^ s), Fz K lam θ (lift s (XX K lam y t) u)
        ≤ Real.exp (θ * ((GG K lam y t : ℝ) - t * lam)) *
          (2 ^ s * Real.exp (θ * (K.V (XX K lam y t) + K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      _ = 2 ^ s * (ρ * Psi K lam θ y t) := by
          rw [Psi]; simp only [ρ, ← Real.exp_add]; rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have h4 := le_of_mul_le_mul_left h3 (by positivity : (0 : ℝ) < 2 ^ s)
  linarith

end potential


/-! ## Most `y` are admissible -/

noncomputable section counting
variable {s H : ℕ} (K : Cert s H) (lam : ℝ) {m : ℕ}

lemma sumPsi_le {N : ℕ} (hm : m = s * N) (hlam : 0 ≤ lam) (θ B : ℝ) (hθ : 0 ≤ θ) (hB : ∀ x, |K.V x| ≤ B)
    (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1)
    (hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) < 1) :
    ∀ t, t + 2 ≤ N → ∑ y : ZMod (2 ^ m), Psi K lam θ y t ≤
      2 ^ m * (Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))) := by
  set ρ := Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2)
  set K0 := Real.exp (θ * (1 + B))
  have h1ρ : 0 < 1 - ρ := by linarith
  have hK0 : 0 ≤ K0 / (1 - ρ) := div_nonneg (Real.exp_pos _).le h1ρ.le
  have hcard : ∀ c : ℝ, ∑ _y : ZMod (2 ^ m), c = 2 ^ m * c := by
    intro c; rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; push_cast; ring
  intro t ht
  induction t with
  | zero =>
    calc ∑ y : ZMod (2 ^ m), Psi K lam θ y 0 ≤ ∑ _y : ZMod (2 ^ m), Real.exp (θ * B) := by
          refine sum_le_sum (fun y _ => ?_)
          rw [Psi, GG_zero]
          apply Real.exp_le_exp.mpr
          have := (abs_le.mp (hB (XX K lam y 0))).2
          push_cast; nlinarith
      _ = 2 ^ m * Real.exp (θ * B) := hcard _
      _ ≤ _ := by gcongr; linarith
  | succ t ih =>
    have hs := Psi_sum_step K lam hm hlam θ B hθ hB hθR t (by omega)
    have ih' := ih (by omega)
    have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
    have hmul : (1 - ρ) * (K0 / (1 - ρ)) = K0 := mul_div_cancel₀ _ (ne_of_gt h1ρ)
    have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
    have hexp : 0 ≤ Real.exp (θ * B) := (Real.exp_pos _).le
    calc ∑ y : ZMod (2 ^ m), Psi K lam θ y (t + 1) ≤ ρ * ∑ y : ZMod (2 ^ m), Psi K lam θ y t + 2 ^ m * K0 := hs
      _ ≤ ρ * (2 ^ m * (Real.exp (θ * B) + K0 / (1 - ρ))) + 2 ^ m * K0 := by gcongr
      _ ≤ 2 ^ m * (Real.exp (θ * B) + K0 / (1 - ρ)) := by
          have : ρ * (Real.exp (θ * B) + K0 / (1 - ρ)) + K0 ≤ Real.exp (θ * B) + K0 / (1 - ρ) := by
            nlinarith
          nlinarith

/-- Markov's inequality on the potential. -/
lemma card_bad_mul_le (θ B c₀ : ℝ) (hB : ∀ x, |K.V x| ≤ B) (hθ : 0 ≤ θ) (t : ℕ) :
    ((univ.filter (fun y : ZMod (2 ^ m) => c₀ < (GG K lam y t : ℝ) - t * lam)).card : ℝ) *
      Real.exp (θ * (c₀ - B)) ≤ ∑ y : ZMod (2 ^ m), Psi K lam θ y t := by
  have h1 := card_nsmul_le_sum (univ.filter (fun y : ZMod (2 ^ m) => c₀ < (GG K lam y t : ℝ) - t * lam))
    (fun y => Psi K lam θ y t) (Real.exp (θ * (c₀ - B))) (fun y hy => by
      rw [mem_filter] at hy
      rw [Psi]; apply Real.exp_le_exp.mpr
      have := (abs_le.mp (hB (XX K lam y t))).1
      apply mul_le_mul_of_nonneg_left _ hθ
      linarith [hy.2])
  rw [nsmul_eq_mul] at h1
  refine h1.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => (Real.exp_pos _).le))

lemma E_step (hlam : 0 ≤ lam) (y : ZMod (2 ^ m)) (t : ℕ) :
    (GG K lam y (t + 1) : ℝ) - (t + 1 : ℕ) * lam ≤ ((GG K lam y t : ℝ) - t * lam) + H + 1 := by
  have hceil : (t : ℝ) * lam ≤ GG K lam y t := by
    have := ceil_le_GG K lam y t
    have h2 := Nat.le_ceil ((t : ℝ) * lam)
    have h3 : ((⌈(t : ℝ) * lam⌉₊ : ℕ) : ℝ) ≤ (GG K lam y t : ℝ) := by exact_mod_cast this
    linarith
  rcases max_choice (GG K lam y t + hh K lam y t) ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ with h | h
  · have hG : GG K lam y (t + 1) = GG K lam y t + hh K lam y t := by rw [GG_succ, h]
    have hH : (hh K lam y t : ℝ) ≤ H := by exact_mod_cast K.hgt_le _
    rw [hG]; push_cast; nlinarith
  · have hG : GG K lam y (t + 1) = ⌈((t + 1 : ℕ) : ℝ) * lam⌉₊ := by rw [GG_succ, h]
    have hc := Nat.ceil_lt_add_one (show 0 ≤ ((t + 1 : ℕ) : ℝ) * lam by positivity)
    rw [hG]
    have : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    linarith

/-- For `N ≥ 3`, at least half of all `y` have `G_N ≤ Nλ + c₀ + 2(H+1)`. -/
lemma good_half {N : ℕ} (hm : m = s * N) (hN : 3 ≤ N) (hlam : 0 ≤ lam) (θ B c₀ : ℝ) (hθ : 0 < θ)
    (hB : ∀ x, |K.V x| ≤ B) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1)
    (hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) < 1)
    (hc₀ : 2 * (Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))) ≤ Real.exp (θ * (c₀ - B))) :
    (2 ^ m : ℝ) ≤ 2 * ((univ.filter (fun y : ZMod (2 ^ m) =>
        (GG K lam y N : ℝ) ≤ N * lam + c₀ + 2 * (H + 1))).card : ℝ) := by
  set M₀ := Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hsum := sumPsi_le K lam hm hlam θ B hθ.le hB hθR hρ M (by omega)
  have hmk := card_bad_mul_le K lam θ B c₀ hB hθ.le M (m := m)
  set bad := univ.filter (fun y : ZMod (2 ^ m) => c₀ < (GG K lam y M : ℝ) - M * lam)
  set good := univ.filter (fun y : ZMod (2 ^ m) => (GG K lam y (M + 2) : ℝ) ≤ ((M + 2 : ℕ) : ℝ) * lam + c₀ + 2 * (H + 1))
  have hM0 : 0 < M₀ := by
    have : 0 < 1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) := by linarith
    positivity
  -- bad count ≤ 2^m / 2
  have hbad : (bad.card : ℝ) * 2 ≤ 2 ^ m := by
    have hE := Real.exp_pos (θ * (c₀ - B))
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have : (bad.card : ℝ) * (2 * M₀) ≤ 2 ^ m * M₀ := by
      calc (bad.card : ℝ) * (2 * M₀) ≤ bad.card * Real.exp (θ * (c₀ - B)) :=
            mul_le_mul_of_nonneg_left hc₀ (Nat.cast_nonneg _)
        _ ≤ _ := hmk.trans hsum
    nlinarith
  -- complement of bad is inside good
  have hsub : univ.filter (fun y : ZMod (2 ^ m) => ¬ (c₀ < (GG K lam y M : ℝ) - M * lam)) ⊆ good := by
    intro y hy
    simp only [good, mem_filter, mem_univ, true_and, not_lt] at hy ⊢
    have e1 := E_step K lam hlam y M
    have e2 := E_step K lam hlam y (M + 1)
    rw [show M + 1 + 1 = M + 2 from rfl] at e2
    push_cast at e1 e2 ⊢
    linarith
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (ZMod (2 ^ m))))
    (fun y : ZMod (2 ^ m) => c₀ < (GG K lam y M : ℝ) - M * lam)
  rw [card_univ, ZMod.card] at hsplit
  have hgood := card_le_card hsub
  have := congrArg (Nat.cast : ℕ → ℝ) hsplit
  push_cast at this
  have hg' : ((univ.filter (fun y : ZMod (2 ^ m) => ¬ (c₀ < (GG K lam y M : ℝ) - M * lam))).card : ℝ) ≤ good.card := by
    exact_mod_cast hgood
  linarith

end counting


/-! ## Counting and density -/

/-- Slack in the top 7-exponent. -/
noncomputable def cstar (H : ℕ) (c₀ : ℝ) : ℕ := ⌈c₀⌉₊ + 2 * H + 2

/-- `n(y) ≤ Cst · 2^{sN}`. -/
noncomputable def Cst (s H : ℕ) (lam c₀ : ℝ) : ℝ :=
  2 ^ s * (7 : ℝ) ^ ((1 + (cstar H c₀ : ℝ))) * ((7 : ℝ) ^ lam / (2 ^ s - (7 : ℝ) ^ lam))

open Classical in
lemma count_N {s H : ℕ} (K : Cert s H) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : (7 : ℝ) ^ lam < 2 ^ s)
    (θ B c₀ : ℝ) (hθ : 0 < θ) (hB : ∀ x, |K.V x| ≤ B) (hθR : θ * ((H : ℝ) + 2 * B + |K.g|) ≤ 1)
    (hρ : Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2) < 1)
    (hc₀ : 2 * (Real.exp (θ * B) + Real.exp (θ * (1 + B)) /
        (1 - Real.exp (θ * (K.g - lam) + θ ^ 2 * ((H : ℝ) + 2 * B + |K.g|) ^ 2))) ≤ Real.exp (θ * (c₀ - B)))
    (N : ℕ) (hN : 3 ≤ N) :
    (2 : ℝ) ^ (s * N) ≤ 2 * (((range (⌊Cst s H lam c₀ * ((2 : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable 7 2)).card : ℝ) := by
  have hgood := good_half K lam (m := s * N) rfl hN hlam0 θ B c₀ hθ hB hθR hρ hc₀
  set good := univ.filter (fun y : ZMod (2 ^ (s * N)) => (GG K lam y N : ℝ) ≤ N * lam + c₀ + 2 * (H + 1))
  set A : ℕ := ⌈(N : ℝ) * lam⌉₊ + cstar H c₀ with hAdef
  have hA : ∀ y ∈ good, GG K lam y N ≤ A := by
    intro y hy
    simp only [good, mem_filter, mem_univ, true_and] at hy
    have h1 := Nat.le_ceil ((N : ℝ) * lam)
    have h2 := Nat.le_ceil c₀
    have : (GG K lam y N : ℝ) ≤ (A : ℝ) := by
      rw [hAdef, cstar]; push_cast; linarith
    exact_mod_cast this
  have hAD : (A : ℝ) ≤ N * lam + (1 + (cstar H c₀ : ℝ)) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) * lam by positivity)
    rw [hAdef]; push_cast; linarith
  set f : ZMod (2 ^ (s * N)) → ℕ := fun y => nval K lam y A N
  have hmaps : Set.MapsTo f good ((range (⌊Cst s H lam c₀ * ((2 : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable 7 2)) := by
    intro y hy
    simp only [mem_coe, mem_filter, mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), nval_representable K lam y (hA y hy)⟩
    have := nval_le_real K lam y (hA y hy) hlam _ hAD
    refine this.trans (le_of_eq ?_)
    rw [Cst]; ring
  have hinj : Set.InjOn f good := fun y hy y' hy' h => nval_inj K lam rfl (hA y hy) (hA y' hy') h
  have hc := card_le_card_of_injOn f hmaps hinj
  have hc' : (good.card : ℝ) ≤ (((range (⌊Cst s H lam c₀ * ((2 : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable 7 2)).card : ℝ) := by
    exact_mod_cast hc
  linarith

open Classical in
/-- **Main theorem (conditional on a certificate).** If a two-block look-ahead potential
certificate for `(7,2)` exists with drift `g < λ` and `7^λ < 2^s`, then the integers
representable as sums of `7^a 2^b` with no summand dividing another have positive lower density. -/
theorem pos_lower_density {s H : ℕ} (K : Cert s H) (lam : ℝ) (hlam0 : 0 ≤ lam) (hg : K.g < lam)
    (hlam : (7 : ℝ) ^ lam < 2 ^ s) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      c * x ≤ (((range (x + 1)).filter (Representable 7 2)).card : ℝ) := by
  -- constants
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
  -- s ≥ 1
  have h7 : (1 : ℝ) ≤ 7 ^ lam := Real.one_le_rpow (by norm_num) hlam0
  have hs1 : (1 : ℝ) < 2 ^ s := lt_of_le_of_lt h7 hlam
  have hC : 0 < Cst s H lam c₀ := by
    rw [Cst]; have : 0 < (2 : ℝ) ^ s - 7 ^ lam := by linarith
    have : (0 : ℝ) < 7 ^ lam := by linarith
    positivity
  set C := Cst s H lam c₀
  have hcount := count_N K lam hlam0 hlam θ B c₀ hθ hB hθR hρ hc₀
  refine ⟨1 / (2 * C * 2 ^ s), by positivity, ⌈C * (2 ^ s) ^ 3⌉₊, fun x hx => ?_⟩
  have hx' : C * (2 ^ s) ^ 3 ≤ (x : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hx)
  -- choose N with C (2^s)^N ≤ x < C (2^s)^(N+1)
  have hex : ∃ n, (x : ℝ) < C * (2 ^ s) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((x : ℝ) / C) hs1
    refine ⟨n, ?_⟩
    have : ((2 : ℝ) ^ s) ^ n ≤ ((2 : ℝ) ^ s) ^ (n + 1) := pow_le_pow_right₀ hs1.le (Nat.le_succ n)
    rw [div_lt_iff₀ hC] at hn
    nlinarith
  classical
  set N := Nat.find hex
  have hNx : (x : ℝ) < C * (2 ^ s) ^ (N + 1) := Nat.find_spec hex
  have hN3 : 3 ≤ N := by
    by_contra hlt
    push Not at hlt
    have : ((2 : ℝ) ^ s) ^ (N + 1) ≤ ((2 : ℝ) ^ s) ^ 3 := pow_le_pow_right₀ hs1.le (by omega)
    nlinarith
  have hxN : C * ((2 : ℝ) ^ s) ^ N ≤ (x : ℝ) := by
    have := Nat.find_min hex (show N - 1 < N by omega)
    push Not at this
    rwa [show N - 1 + 1 = N by omega] at this
  have hcN := hcount N hN3
  -- monotonicity of the count
  have hmono : (((range (⌊C * ((2 : ℝ) ^ s) ^ N⌋₊ + 1)).filter (Representable 7 2)).card : ℝ) ≤
      (((range (x + 1)).filter (Representable 7 2)).card : ℝ) := by
    have hfl : ⌊C * ((2 : ℝ) ^ s) ^ N⌋₊ ≤ x := Nat.floor_le_of_le hxN
    exact_mod_cast card_le_card (filter_subset_filter _ (range_subset_range.mpr (Nat.succ_le_succ hfl)))
  have h2 : (2 : ℝ) ^ (s * N) = (2 ^ s) ^ N := by rw [pow_mul]
  rw [h2] at hcN
  have hpos : (0 : ℝ) < 2 * C * 2 ^ s := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  rw [pow_succ] at hNx
  nlinarith


/-! ## The (7,2) instance: the only external input is the certificate checked by `verify.c` -/

lemma seven_rpow_lt : (7 : ℝ) ^ ((286 : ℝ) / 73) < 2 ^ 11 := by
  by_contra h
  push Not at h
  have h1 : ((2 : ℝ) ^ 11) ^ 73 ≤ ((7 : ℝ) ^ ((286 : ℝ) / 73)) ^ 73 :=
    pow_le_pow_left₀ (by positivity) h 73
  rw [← Real.rpow_natCast ((7 : ℝ) ^ ((286 : ℝ) / 73)), ← Real.rpow_mul (by norm_num),
    show (286 : ℝ) / 73 * ((73 : ℕ) : ℝ) = ((286 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  -- 7^286 = (7^26)^11 < (2^73)^11 = (2^11)^73, from 7^26 < 2^73
  have h2 : (7 : ℝ) ^ 286 < ((2 : ℝ) ^ 11) ^ 73 := by
    have e1 : (7 : ℝ) ^ 286 = ((7 : ℝ) ^ 26) ^ 11 := by rw [← pow_mul]
    have e2 : ((2 : ℝ) ^ 11) ^ 73 = ((2 : ℝ) ^ 73) ^ 11 := by rw [← pow_mul, ← pow_mul]
    rw [e1, e2]
    exact pow_lt_pow_left₀ (by norm_num) (by positivity) (by norm_num)
  exact absurd h1 (not_le.mpr h2)

open Classical in
/-- **Erdős #1110, (7,2), conditional on the machine-checked certificate.** If there is a
certificate with block size `s = 11`, heights `≤ 10` and drift `g = 8385274094 / 2^31`
(what `verify.c` / `verify2.c` check for the table `V_s11_it8.bin`), then the integers that are
sums of numbers `7^k 2^l` none of which divides another have positive lower density. -/
theorem erdos1110_72_density (h : ∃ K : Cert 11 10, K.g = 8385274094 / 2 ^ 31) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      c * x ≤ (((range (x + 1)).filter (Representable 7 2)).card : ℝ) := by
  obtain ⟨K, hK⟩ := h
  refine pos_lower_density K ((286 : ℝ) / 73) (by norm_num) ?_ seven_rpow_lt
  rw [hK]; norm_num

end E1110

namespace E1110
/-- Sanity check: `Cert` is inhabited (toy certificate with a useless drift `g = 1`, s = 1). -/
def toyCert : Cert 1 1 where
  ch z := if z.val % 2 = 1 then {(0, 0)} else ∅
  hgt z := if z.val % 2 = 1 then 1 else 0
  V _ := 0
  g := 1
  chain z a ha b hb h := by
    split_ifs at ha hb <;> simp_all
  inj z a ha b hb h := by
    split_ifs at ha hb <;> simp_all
  alpha_lt z a ha := by
    split_ifs at ha <;> simp_all
  gamma_lt z a ha := by
    split_ifs at ha with h <;> simp_all
  hgt_le z := by split_ifs <;> norm_num
  res z := by
    revert z
    simp only [v3, cval]
    decide
  drift x := by
    simp only [add_zero, zero_add]
    have : ∀ u : ZMod (2 ^ 1), ((if (lift 1 x u).val % 2 = 1 then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      intro u; split_ifs <;> norm_num
    calc _ ≤ ∑ _u : ZMod (2 ^ 1), (1 : ℝ) := Finset.sum_le_sum (fun u _ => this u)
      _ = 2 ^ 1 * 1 := by simp [ZMod.card]
end E1110

#print axioms E1110.pos_lower_density
#print axioms E1110.erdos1110_72_density
