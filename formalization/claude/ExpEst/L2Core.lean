import ExpEst.Thm53i

/-!
# The arithmetic core of Claims 5.3C and 5.4C over `ℚ`

For nonzero coprime integers `A, B, C` with `A + B + C = 0`,
`j = 2^8 N³ / (ABC)²` with `N = A² + AB + B²` coprime to `ABC`, so
`(ABC)² ≤ 2^8 · den(j)` and hence `h^non(j) = log den(j) ≥ 2 log|ABC| - 8 log 2`.
This is the `ℚ`-case of inequality (1) in the proof of Theorem 5.3 combined with (2) of
Claim 5.4C (the paper derives it from Lemma 1.3, Proposition 1.8 and Remark 1.10.1).
-/

namespace ExpEst

open Real

theorem isCoprime_third {A B : ℤ} (h : IsCoprime A B) : IsCoprime (-A - B) A ∧ IsCoprime (-A - B) B := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨-v, u - v, by linear_combination huv⟩, ⟨-u, v - u, by linear_combination huv⟩⟩

/-- `N = A² + AB + B²` is coprime to `ABC`. -/
theorem isCoprime_N {A B C : ℤ} (h : IsCoprime A B) (habc : A + B + C = 0) :
    IsCoprime (A * B * C) (A ^ 2 + A * B + B ^ 2) := by
  have hC : C = -A - B := by linarith
  have hA : IsCoprime A (A ^ 2 + A * B + B ^ 2) := by
    have e : A ^ 2 + A * B + B ^ 2 = B ^ 2 + A * (A + B) := by ring
    rw [e, IsCoprime.add_mul_left_right_iff]
    exact h.pow_right
  have hB : IsCoprime B (A ^ 2 + A * B + B ^ 2) := by
    have e : A ^ 2 + A * B + B ^ 2 = A ^ 2 + B * (A + B) := by ring
    rw [e, IsCoprime.add_mul_left_right_iff]
    exact h.symm.pow_right
  have hCN : IsCoprime C (A ^ 2 + A * B + B ^ 2) := by
    have e : A ^ 2 + A * B + B ^ 2 = -(A * B) + C * C := by rw [hC]; ring
    rw [e, IsCoprime.add_mul_left_right_iff, IsCoprime.neg_right_iff]
    obtain ⟨h1, h2⟩ := isCoprime_third h
    rw [hC]
    exact h1.mul_right h2
  exact (hA.mul_left hB).mul_left hCN

/-- `(ABC)² ≤ 2^8 · den(j)`. -/
theorem den_bound {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (h : IsCoprime A B)
    (habc : A + B + C = 0) :
    (A * B * C) ^ 2 ≤
      256 * ((256 * ((A : ℚ) ^ 2 + A * B + B ^ 2) ^ 3 / ((A : ℚ) * B * C) ^ 2).den : ℤ) := by
  set N : ℤ := A ^ 2 + A * B + B ^ 2 with hN
  set M : ℤ := (A * B * C) ^ 2 with hM
  set j : ℚ := 256 * ((A : ℚ) ^ 2 + A * B + B ^ 2) ^ 3 / ((A : ℚ) * B * C) ^ 2 with hj
  have hM0 : ((A : ℚ) * B * C) ^ 2 ≠ 0 := by positivity
  have key : (j.num : ℚ) * M = 256 * N ^ 3 * j.den := by
    have h1 := Rat.mul_den_eq_num j
    rw [← h1, hj, hM, hN]
    push_cast
    field_simp
  have key' : j.num * M = 256 * N ^ 3 * j.den := by exact_mod_cast key
  have hdvd : M ∣ (256 * (j.den : ℤ)) * N ^ 3 := ⟨j.num, by linear_combination -key'⟩
  have hcop : IsCoprime M (N ^ 3) := (isCoprime_N h habc).pow
  have hdvd' : M ∣ 256 * (j.den : ℤ) := hcop.dvd_of_dvd_mul_right hdvd
  have hpos : 0 < 256 * (j.den : ℤ) := by positivity
  exact Int.le_of_dvd hpos hdvd'

/-- `h^non(j(E_{A,B,C})) ≥ 2 log|ABC| - 8 log 2` for coprime integers. -/
theorem hnon_j_ge {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (h : IsCoprime A B)
    (habc : A + B + C = 0) :
    2 * Real.log |(A : ℝ) * B * C| - 8 * Real.log 2 ≤
      hnon (256 * ((A : ℚ) ^ 2 + A * B + B ^ 2) ^ 3 / ((A : ℚ) * B * C) ^ 2) := by
  rw [hnon_eq_log_den]
  set d := (256 * ((A : ℚ) ^ 2 + A * B + B ^ 2) ^ 3 / ((A : ℚ) * B * C) ^ 2).den with hd
  have hb := den_bound hA hB hC h habc
  rw [← hd] at hb
  have hbR : ((A : ℝ) * B * C) ^ 2 ≤ 256 * (d : ℝ) := by exact_mod_cast hb
  have hX : 0 < |(A : ℝ) * B * C| := by positivity
  have hd0 : (0 : ℝ) < d := by positivity
  have h1 : Real.log (((A : ℝ) * B * C) ^ 2) ≤ Real.log (256 * (d : ℝ)) :=
    Real.log_le_log (by positivity) hbR
  rw [← sq_abs, Real.log_pow, Real.log_mul (by norm_num) hd0.ne',
    show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow] at h1
  push_cast at h1
  linarith

/-- For nonzero integers with `x + y + z = 0`: `z² ≤ 2|xyz|`. -/
theorem sq_le_two_abs_mul {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (h : x + y + z = 0) :
    z ^ 2 ≤ 2 * |x * y * z| := by
  have hz : |z| ≤ |x| + |y| := by
    have : z = -(x + y) := by linarith
    rw [this, abs_neg]
    exact abs_add_le x y
  have hx1 : 1 ≤ |x| := Int.one_le_abs hx
  have hy1 : 1 ≤ |y| := Int.one_le_abs hy
  have hxy : |x| + |y| ≤ 2 * (|x| * |y|) := by nlinarith
  rw [abs_mul, abs_mul, ← sq_abs z]
  have hz0 : 0 ≤ |z| := abs_nonneg z
  nlinarith

/-- `max{|A|, |B|, |C|}² ≤ 2|ABC|`. -/
theorem max_sq_le {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (habc : A + B + C = 0) :
    (max |(A : ℝ)| (max |(B : ℝ)| |(C : ℝ)|)) ^ 2 ≤ 2 * |(A : ℝ) * B * C| := by
  have e1 := sq_le_two_abs_mul hB hC (by linarith : B + C + A = 0)
  have e2 := sq_le_two_abs_mul hA hC (by linarith : A + C + B = 0)
  have e3 := sq_le_two_abs_mul hA hB habc
  have r1 : (A : ℝ) ^ 2 ≤ 2 * |(A : ℝ) * B * C| := by
    have : ((A ^ 2 : ℤ) : ℝ) ≤ ((2 * |B * C * A| : ℤ) : ℝ) := by exact_mod_cast e1
    push_cast at this
    have hh : |(B : ℝ) * C * A| = |(A : ℝ) * B * C| := by ring_nf
    linarith
  have r2 : (B : ℝ) ^ 2 ≤ 2 * |(A : ℝ) * B * C| := by
    have : ((B ^ 2 : ℤ) : ℝ) ≤ ((2 * |A * C * B| : ℤ) : ℝ) := by exact_mod_cast e2
    push_cast at this
    have hh : |(A : ℝ) * C * B| = |(A : ℝ) * B * C| := by ring_nf
    linarith
  have r3 : (C : ℝ) ^ 2 ≤ 2 * |(A : ℝ) * B * C| := by
    have : ((C ^ 2 : ℤ) : ℝ) ≤ ((2 * |A * B * C| : ℤ) : ℝ) := by exact_mod_cast e3
    push_cast at this
    linarith
  rcases le_total |(B : ℝ)| |(C : ℝ)| with h1 | h1 <;>
  rcases le_total |(A : ℝ)| (max |(B : ℝ)| |(C : ℝ)|) with h2 | h2
  · rw [max_eq_right h2, max_eq_right h1, sq_abs]; exact r3
  · rw [max_eq_left h2, sq_abs]; exact r1
  · rw [max_eq_right h2, max_eq_left h1, sq_abs]; exact r2
  · rw [max_eq_left h2, sq_abs]; exact r1

end ExpEst
