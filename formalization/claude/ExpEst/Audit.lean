import ExpEst.L2Link

/-!
# Audit of the L1 formalization

1. Axioms of the main results.
2. The hypothesis `Thm53ii_Q_int` holds on every triple of height at most `exp(h₁(1)/4)`
   (`thm53_small`): its right-hand side is at least `2^(5/2) · exp(h₁(1)/4)`.  This checks a
   height range only; consistency of the universal hypothesis is not established here.
3. Negative control: the integral form *without* the coprimality condition (a different
   statement) is false (`not_thm53_noCoprime`), so the coprimality guard is doing real work.
-/

namespace ExpEst

open Real

/-- The hypothesis holds for every triple with `max{|a|,|b|,|c|} ≤ exp(h₁(1)/4)`
(about `exp(8.5·10^29)`); a counterexample would need a larger height.  This is a bound on the
height range checked, not a proof of the universal statement. -/
theorem thm53_small (a b c : ℤ) (hsmall : max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|) ≤ exp (h1 1 / 4)) :
    max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|) ≤
      2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) ((rad (a * b * c) : ℝ) ^ 3) := by
  have h5 : (1 : ℝ) ≤ 2 ^ ((5 : ℝ) / 2) := one_le_rpow (by norm_num) (by norm_num)
  have hE : 0 ≤ exp (h1 1 / 4) := (exp_pos _).le
  calc max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|) ≤ exp (h1 1 / 4) := hsmall
    _ ≤ max (exp (h1 1 / 4)) ((rad (a * b * c) : ℝ) ^ 3) := le_max_left _ _
    _ ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) ((rad (a * b * c) : ℝ) ^ 3) :=
        le_mul_of_one_le_left (le_trans hE (le_max_left _ _)) h5

/-- The same statement without `IsCoprime a b`. -/
def Thm53ii_Q_int_noCoprime : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 →
    (max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|)) ≤
      2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) ((rad (a * b * c) : ℝ) ^ 3)

/-- Negative control: without coprimality the statement is false
(take `(2^n, 2^n, -2^(n+1))`, whose radical is `2`). -/
theorem not_thm53_noCoprime : ¬ Thm53ii_Q_int_noCoprime := by
  intro H
  set B : ℝ := 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) 8 with hB
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  have h := H (2 ^ n) (2 ^ n) (-2 ^ (n + 1)) (by positivity) (by positivity)
    (neg_ne_zero.mpr (by positivity)) (by ring)
  have hrad : rad ((2 : ℤ) ^ n * 2 ^ n * (-2 ^ (n + 1))) = 2 := by
    have : ((2 : ℤ) ^ n * 2 ^ n * (-2 ^ (n + 1))).natAbs = 2 ^ (3 * n + 1) := by
      rw [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_mul]
      simp only [Int.natAbs_pow]
      norm_num
      ring
    rw [rad, this, Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
    simp
  rw [hrad] at h
  push_cast at h
  have hl : (2 : ℝ) ^ n < max |((2 : ℝ) ^ n)| (max |((2 : ℝ) ^ n)| |(-(2 : ℝ) ^ (n + 1))|) := by
    apply lt_max_of_lt_right
    apply lt_max_of_lt_right
    rw [abs_neg, abs_of_pos (by positivity), pow_succ]
    have : (0 : ℝ) < 2 ^ n := by positivity
    linarith
  norm_num at h
  linarith

/-- The paper-form hypothesis `Thm53ii_Q` holds for every triple of height at most
`exp(h₁(1)/4)`; a counterexample would have to be a counterexample to this explicit `ε = 1` inequality,
of height above `exp(8.5·10^29)`. -/
theorem thm53Q_small (a b c : ℚ) (hsmall : Height.mulHeight ![a, b, c] ≤ exp (h1 1 / 4)) :
    Height.mulHeight ![a, b, c] ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) (radQ a b c ^ 3) := by
  have h5 : (1 : ℝ) ≤ 2 ^ ((5 : ℝ) / 2) := one_le_rpow (by norm_num) (by norm_num)
  have hE : 0 ≤ exp (h1 1 / 4) := (exp_pos _).le
  calc Height.mulHeight ![a, b, c] ≤ exp (h1 1 / 4) := hsmall
    _ ≤ max (exp (h1 1 / 4)) (radQ a b c ^ 3) := le_max_left _ _
    _ ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) (radQ a b c ^ 3) :=
        le_mul_of_one_le_left (le_trans hE (le_max_left _ _)) h5

end ExpEst

/-! ## Axioms -/

#print axioms ExpEst.lemma55
#print axioms ExpEst.lemma55_exact
#print axioms ExpEst.lemma55_paper
#print axioms ExpEst.Q_eq_lemma55
#print axioms ExpEst.lemma56_i
#print axioms ExpEst.lemma56_ii
#print axioms ExpEst.lemma56_iii
#print axioms ExpEst.lemma56_iii'
#print axioms ExpEst.lemma57
#print axioms ExpEst.cor58
#print axioms ExpEst.not_thm53_noCoprime
#print axioms ExpEst.thm53ii_Q_to_int
#print axioms ExpEst.cor58_Q
#print axioms ExpEst.hnon_eq_log_den
#print axioms ExpEst.j_Eabc
#print axioms ExpEst.thm53ii_of_i
#print axioms ExpEst.thm54
#print axioms ExpEst.thm53_i_imp_ii
#print axioms ExpEst.thm53i_imp_thm54
#print axioms ExpEst.cor58_of_thm53i
#print axioms ExpEst.example_hnon
