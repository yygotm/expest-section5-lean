import Mathlib

/-!
# ExpEst Lemma 5.5

Mochizuki–Fesenko–Hoshi–Minamide–Porowski, *Explicit estimates in inter-universal
Teichmüller theory*, Kodai Math. J. 45 (2022), §5.

`Q p r s = ∑_{i<p} r^i (-s)^(p-1-i)` is a polynomial in `r, s`; for odd `p`,
`(r + s) * Q p r s = r^p + s^p` (`add_mul_Q`).  So when `r + s ≠ 0` it is the integer
`(r^p + s^p)(r + s)⁻¹` of the paper.  (When `r + s = 0` the paper's quotient is undefined,
while `Q p r (-r) = p r^(p-1)`.)

Lemma 5.5 of the paper (odd `p ≥ 3`, `r + s ≠ 0`) is the identity
  `(r^p + s^p)(r + s)⁻¹ = p s^(p-1) - (r + s) T`,  `T = ∑_{i=0}^{p-2} (-1)^(i+1) (i+1) r^(p-2-i) s^i`.
It is proved below as `lemma55_exact` (in any field) and `Q_eq_lemma55` (for `Q` over `ℤ`),
with `T = T55 p r s`.  The uses of Lemma 5.5 in §5 (Lemma 5.6 (i), (iii); Lemma 5.7, case
`p ∣ z`) only need the divisibility `(r + s) ∣ Q p r s - p s^(p-1)`, stated as `lemma55`
(valid for every odd `p`, including `r + s = 0`).
-/

namespace ExpEst

open Finset

/-- `Q p r s = ∑_{i<p} r^i (-s)^(p-1-i)`; equals `(r^p + s^p)/(r + s)` for odd `p` when `r + s ≠ 0`. -/
def Q (p : ℕ) (r s : ℤ) : ℤ := ∑ i ∈ range p, r ^ i * (-s) ^ (p - 1 - i)

/-- `(r + s) * Q p r s = r^p + s^p` for odd `p` (geometric sum with `y = -s`). -/
theorem add_mul_Q {p : ℕ} (hp : Odd p) (r s : ℤ) : (r + s) * Q p r s = r ^ p + s ^ p := by
  have h := geom_sum₂_mul r (-s) p
  rw [Odd.neg_pow hp, sub_neg_eq_add, sub_neg_eq_add] at h
  rw [Q, mul_comm, h]

/-- Lemma 5.5 (divisibility form): `(r + s) ∣ Q p r s - p * s^(p-1)` for odd `p`. -/
theorem lemma55 {p : ℕ} (hp : Odd p) (r s : ℤ) : (r + s) ∣ Q p r s - p * s ^ (p - 1) := by
  have hev : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by omega⟩
  have h1 : (p : ℤ) * s ^ (p - 1) = ∑ i ∈ range p, (-s) ^ i * (-s) ^ (p - 1 - i) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-s) ^ (p - 1))]
    · simp [Even.neg_pow hev]
    · intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
  rw [h1, Q, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  rw [← sub_mul]
  apply Dvd.dvd.mul_right
  simpa [sub_neg_eq_add] using sub_dvd_pow_sub_pow r (-s) i

/-! ## Lemma 5.5, the identity as stated in the paper -/

/-- `S55 n r u = ∑_{i=0}^{n} (i+1) u^i r^(n-i)`. -/
def S55 {R : Type*} [CommRing R] (n : ℕ) (r u : R) : R :=
  ∑ i ∈ range (n + 1), ((i : R) + 1) * u ^ i * r ^ (n - i)

theorem S55_succ {R : Type*} [CommRing R] (n : ℕ) (r u : R) :
    S55 (n + 1) r u = r * S55 n r u + ((n : R) + 2) * u ^ (n + 1) := by
  unfold S55
  rw [Finset.sum_range_succ (n := n + 1), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  · rw [Nat.sub_self, pow_zero]
    push_cast
    ring

/-- `(r - u)² · S55 n r u = r^(n+2) - (n+2) r u^(n+1) + (n+1) u^(n+2)`
(the derivative of a geometric sum, as in the paper's proof). -/
theorem S55_mul {R : Type*} [CommRing R] (n : ℕ) (r u : R) :
    (r - u) ^ 2 * S55 n r u =
      r ^ (n + 2) - ((n : R) + 2) * r * u ^ (n + 1) + ((n : R) + 1) * u ^ (n + 2) := by
  induction n with
  | zero =>
    simp only [S55, zero_add, Finset.sum_range_one, Nat.cast_zero, pow_zero, Nat.sub_self]
    ring
  | succ n ih =>
    rw [S55_succ]
    push_cast
    linear_combination r * ih

/-- The finite sum `T = ∑_{i=0}^{p-2} (-1)^(i+1) (i+1) r^(p-2-i) s^i` of Lemma 5.5. -/
def T55 {R : Type*} [CommRing R] (p : ℕ) (r s : R) : R :=
  ∑ i ∈ range (p - 1), (-1) ^ (i + 1) * ((i : R) + 1) * r ^ (p - 2 - i) * s ^ i

theorem T55_eq {R : Type*} [CommRing R] (n : ℕ) (r s : R) : T55 (n + 2) r s = -S55 n r (-s) := by
  unfold T55 S55
  rw [show n + 2 - 1 = n + 1 by omega, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show n + 2 - 2 - i = n - i by omega, neg_pow s i, pow_succ]
  ring

/-- `(r + s)(p s^(p-1) - (r + s) T) = r^p + s^p` for odd `p ≥ 3`, in any commutative ring. -/
theorem add_mul_lemma55 {R : Type*} [CommRing R] {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (r s : R) :
    (r + s) * ((p : R) * s ^ (p - 1) - (r + s) * T55 p r s) = r ^ p + s ^ p := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by omega⟩
  have hn : Odd n := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k - 1, by omega⟩
  rw [T55_eq]
  have h := S55_mul n r (-s)
  rw [sub_neg_eq_add, hn.add_one.neg_pow s, hp.neg_pow s] at h
  rw [show n + 2 - 1 = n + 1 by omega]
  push_cast
  linear_combination h

/-- **Lemma 5.5** as stated in the paper: for odd `p ≥ 3` and `r + s ≠ 0`,
`(r^p + s^p)(r + s)⁻¹ = p s^(p-1) - (r + s) ∑_{i=0}^{p-2} (-1)^(i+1) (i+1) r^(p-2-i) s^i`
(in any field; the paper's case is `r, s ∈ ℤ ⊆ ℚ`, see `lemma55_paper`). -/
theorem lemma55_exact {K : Type*} [Field K] {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) {r s : K}
    (hrs : r + s ≠ 0) :
    (r ^ p + s ^ p) / (r + s) = (p : K) * s ^ (p - 1) - (r + s) * T55 p r s := by
  rw [← add_mul_lemma55 hp hp3 r s, mul_div_cancel_left₀ _ hrs]

/-- Lemma 5.5 for integers `r, s` with `r + s ≠ 0`, the quotient taken in `ℚ`. -/
theorem lemma55_paper {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) {r s : ℤ} (hrs : r + s ≠ 0) :
    ((r : ℚ) ^ p + (s : ℚ) ^ p) / ((r : ℚ) + s) =
      (p : ℚ) * (s : ℚ) ^ (p - 1) - ((r : ℚ) + s) * T55 p (r : ℚ) (s : ℚ) :=
  lemma55_exact hp hp3 (by exact_mod_cast hrs)

/-- The same identity for the integer `Q p r s` (`r + s ≠ 0`). -/
theorem Q_eq_lemma55 {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) {r s : ℤ} (hrs : r + s ≠ 0) :
    Q p r s = p * s ^ (p - 1) - (r + s) * T55 p r s :=
  mul_left_cancel₀ hrs (by rw [add_mul_Q hp, add_mul_lemma55 hp hp3])

end ExpEst
