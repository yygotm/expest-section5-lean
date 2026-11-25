import ExpEst.L2Core

/-!
# L2: Theorem 5.3 (i) ⇒ (ii) and Theorem 5.4 over `ℚ`

Both are proved triple by triple: the hypothesis is the inequality of Theorem 5.3 (i) for
the given `(a, b, c)` and `ε`, not for all triples.

Route (over `ℚ` the paper's Claims 5.3A–C and 5.4A–C reduce to the integer core of
`L2Core.lean`): scale `(a, b, c)` to a primitive integer triple `(A, B, C)`; then `j` and
`H_ℚ` do not change, `h^non(j) ≥ 2 log|ABC| - 8 log 2` and `max{|A|,|B|,|C|}² ≤ 2|ABC|`.
-/

namespace ExpEst

open Real Height

/-- `j` as a rational function of the triple. -/
def jform (a b c : ℚ) : ℚ := 256 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a * b * c) ^ 2

theorem jform_smul {t : ℚ} (ht : t ≠ 0) (a b c : ℚ) :
    jform (t * a) (t * b) (t * c) = jform a b c := by
  unfold jform
  rcases eq_or_ne (a * b * c) 0 with h | h
  · have : t * a * (t * b) * (t * c) = 0 := by rw [show t * a * (t * b) * (t * c) = t ^ 3 * (a * b * c) by ring, h, mul_zero]
    simp [this, h]
  · field_simp

/-- `rad_ℚ(a, b, c) ≥ 1`. -/
theorem one_le_radQ (a b c : ℚ) : 1 ≤ radQ a b c := by
  classical
  rw [radQ, finprod_def]
  split_ifs with hfin
  · refine Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
      (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl ?_
    intro q _
    split_ifs
    · exact le_rfl
    · exact_mod_cast q.2.one_lt.le
  · exact le_rfl

/-- For a primitive triple, `H_ℚ(A, B, C) ≤ max{|A|, |B|, |C|}`. -/
theorem mulHeight_le_max_abs {A B C : ℤ} (hab : IsCoprime A B) :
    mulHeight ![(A : ℚ), (B : ℚ), (C : ℚ)] ≤ max |(A : ℝ)| (max |(B : ℝ)| |(C : ℝ)|) := by
  have hcomp : ![(A : ℚ), (B : ℚ), (C : ℚ)] = ((↑) : ℤ → ℚ) ∘ ![A, B, C] := by
    ext i
    fin_cases i <;> rfl
  rw [hcomp, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (gcd_fin3_eq_one hab)]
  have hs : (⨆ i, |![A, B, C] i|) ≤ max |A| (max |B| |C|) := by
    apply ciSup_le
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have : ((⨆ i, |![A, B, C] i| : ℤ) : ℝ) ≤ ((max |A| (max |B| |C|) : ℤ) : ℝ) := by exact_mod_cast hs
  simpa using this

/-- A rational triple with each coordinate nonzero and sum `0` is a nonzero multiple of a
primitive integer triple. -/
theorem primitive_rep {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) :
    ∃ (t : ℚ) (A B C : ℤ), t ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ A + B + C = 0 ∧ IsCoprime A B ∧
      a = t * A ∧ b = t * B ∧ c = t * C := by
  set q := a / b with hq
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  refine ⟨b / q.den, q.num, q.den, -(q.num + q.den), div_ne_zero hb hd, ?_, by exact_mod_cast q.den_nz,
    ?_, by ring, ?_, ?_, ?_, ?_⟩
  · rw [Rat.num_ne_zero, hq]; exact div_ne_zero ha hb
  · intro h0
    apply hc
    have e : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have : (q.num : ℚ) + q.den = 0 := by
      have := congrArg (fun z : ℤ => (z : ℚ)) h0
      push_cast at this
      linarith
    rw [e, hq] at this
    have hq' : (a / b + 1) * q.den = 0 := by linarith
    rcases mul_eq_zero.mp hq' with h1 | h1
    · field_simp at h1
      linarith
    · exact absurd h1 hd
  · rw [Int.isCoprime_iff_gcd_eq_one]
    exact q.reduced
  · have e : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    rw [e, hq]
    field_simp
  · push_cast
    field_simp
  · have e : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    push_cast
    rw [e, hq]
    field_simp
    linarith

/-- The common lower bound (Claim 5.3C over `ℚ`, in additive form):
`(2/3) log max{|A|,|B|,|C|} - (5/3) log 2 ≤ (1/6) h^non(j)`. -/
theorem claim53C {A B C : ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (h : IsCoprime A B)
    (habc : A + B + C = 0) :
    (2 / 3) * Real.log (max |(A : ℝ)| (max |(B : ℝ)| |(C : ℝ)|)) - (5 / 3) * Real.log 2 ≤
      (1 / 6) * hnon (jform A B C) := by
  have h1 := hnon_j_ge hA hB hC h habc
  have h2 := max_sq_le hA hB hC habc
  set Hm := max |(A : ℝ)| (max |(B : ℝ)| |(C : ℝ)|) with hHm
  have hHm0 : 0 < Hm := lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hA)) (le_max_left _ _)
  have hX : 0 < |(A : ℝ) * B * C| := by positivity
  have h3 : Real.log (Hm ^ 2) ≤ Real.log (2 * |(A : ℝ) * B * C|) := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul (by norm_num) hX.ne'] at h3
  unfold jform
  push_cast at h1 h3 ⊢
  linarith

/-- **Theorem 5.3 (i) ⇒ (ii)** for `L = ℚ` (`d = 1`, `Δ_ℚ = 1`), triple by triple. -/
theorem thm53ii_of_i {ε : ℝ} (hε : 0 < ε) {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : a + b + c = 0)
    (hi : (1 / 6 : ℝ) * hnon (@WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc)) ≤
      max ((1 + ε) * Real.log (radQ a b c)) ((1 / 6 : ℝ) * h1 ε)) :
    mulHeight ![a, b, c] ≤
        2 ^ ((5 : ℝ) / 2) * max (exp (h1 ε / 4)) (radQ a b c ^ (3 * (1 + ε) / 2)) ∧
      2 ^ ((5 : ℝ) / 2) * max (exp (h1 ε / 4)) (radQ a b c ^ (3 * (1 + ε) / 2)) ≤
        2 ^ ((5 : ℝ) / 2) * exp (h1 ε / 4) * radQ a b c ^ (3 * (1 + ε) / 2) := by
  obtain ⟨t, A, B, C, ht, hA, hB, hC, hABC, hcop, rfl, rfl, rfl⟩ := primitive_rep ha hb hc habc
  set R := radQ (t * A) (t * B) (t * C) with hR
  have hR1 : 1 ≤ R := one_le_radQ _ _ _
  have hR0 : 0 < R := by linarith
  have hh1 : 0 ≤ h1 ε := by unfold h1; have := rpow_nonneg hε.le (-(166 : ℝ) / 81); positivity
  -- `j` and `H` are unchanged by scaling
  rw [j_Eabc ha hb hc habc, ← jform, jform_smul ht] at hi
  have hH : mulHeight ![t * (A : ℚ), t * B, t * C] = mulHeight ![(A : ℚ), (B : ℚ), (C : ℚ)] := by
    have : ![t * (A : ℚ), t * B, t * C] = t • ![(A : ℚ), (B : ℚ), (C : ℚ)] := by
      ext i; fin_cases i <;> simp
    rw [this, mulHeight_smul_eq_mulHeight _ ht]
  have hC53 := claim53C hA hB hC hcop hABC
  set Hm := max |(A : ℝ)| (max |(B : ℝ)| |(C : ℝ)|) with hHm
  have hHm0 : 0 < Hm := lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hA)) (le_max_left _ _)
  -- log Hm ≤ (5/2) log 2 + max{(3(1+ε)/2) log R, h₁(ε)/4}
  have hlog : Real.log Hm ≤ (5 / 2) * Real.log 2 +
      max ((3 * (1 + ε) / 2) * Real.log R) (h1 ε / 4) := by
    have e : max ((3 * (1 + ε) / 2) * Real.log R) (h1 ε / 4) =
        (3 / 2) * max ((1 + ε) * Real.log R) ((1 / 6) * h1 ε) := by
      rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      congr 1 <;> ring
    rw [e]
    linarith
  have hexp : Hm ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 ε / 4)) (R ^ (3 * (1 + ε) / 2)) := by
    calc Hm = exp (Real.log Hm) := (exp_log hHm0).symm
      _ ≤ exp ((5 / 2) * Real.log 2 + max ((3 * (1 + ε) / 2) * Real.log R) (h1 ε / 4)) :=
          exp_le_exp.mpr hlog
      _ = 2 ^ ((5 : ℝ) / 2) * max (exp (h1 ε / 4)) (R ^ (3 * (1 + ε) / 2)) := by
          rw [exp_add, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), rpow_def_of_pos hR0,
            Real.exp_monotone.map_max]
          rw [max_comm]
          ring_nf
  have hEm : 1 ≤ exp (h1 ε / 4) := one_le_exp (by positivity)
  have hRm : 1 ≤ R ^ (3 * (1 + ε) / 2) := one_le_rpow hR1 (by positivity)
  refine ⟨?_, ?_⟩
  · rw [hH]
    exact (mulHeight_le_max_abs hcop).trans hexp
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le_mul_of_one_le hEm hRm) (by positivity)

/-- **Theorem 5.4** (effective Szpiro over `ℚ`), from Theorem 5.3 (i) for the same triple. -/
theorem thm54 {ε : ℝ} (hε : 0 < ε) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : a + b + c = 0) (hcop : IsCoprime a b)
    (hi : (1 / 6 : ℝ) * hnon (@WeierstrassCurve.j ℚ _ (Eabc a b c)
        (Eabc_isElliptic (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
          (by exact_mod_cast habc))) ≤
      max ((1 + ε) * Real.log (radQ a b c)) ((1 / 6 : ℝ) * h1 ε)) :
    |((a * b * c : ℤ) : ℝ)| ≤
        2 ^ 4 * max (exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81))) ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε))) ∧
      2 ^ 4 * max (exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81))) ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε))) ≤
        2 ^ 4 * exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81)) * (rad (a * b * c) : ℝ) ^ (3 * (1 + ε)) := by
  rw [j_Eabc (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast habc)] at hi
  have h1' := hnon_j_ge ha hb hc hcop habc
  set R := radQ a b c with hR
  have hR1 : 1 ≤ R := one_le_radQ _ _ _
  have hR0 : 0 < R := by linarith
  have hRr : R ≤ (rad (a * b * c) : ℝ) := radQ_le_rad a b c (by positivity)
  set r : ℝ := (rad (a * b * c) : ℝ) with hr
  have hr0 : 0 < r := by linarith
  have hh : h1 ε / 2 = 1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81) := by unfold h1; ring
  have hh1 : 0 ≤ h1 ε := by unfold h1; have := rpow_nonneg hε.le (-(166 : ℝ) / 81); positivity
  have hX : 0 < |(a : ℝ) * b * c| := by positivity
  have hlogR : Real.log R ≤ Real.log r := Real.log_le_log hR0 hRr
  have hlog : Real.log |(a : ℝ) * b * c| ≤ 4 * Real.log 2 +
      max ((3 * (1 + ε)) * Real.log r) (h1 ε / 2) := by
    have hm : max ((1 + ε) * Real.log R) ((1 / 6) * h1 ε) ≤
        max ((1 + ε) * Real.log r) ((1 / 6) * h1 ε) :=
      max_le_max (mul_le_mul_of_nonneg_left hlogR (by linarith)) le_rfl
    have e : max ((3 * (1 + ε)) * Real.log r) (h1 ε / 2) =
        3 * max ((1 + ε) * Real.log r) ((1 / 6) * h1 ε) := by
      rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1 <;> ring
    rw [e]
    linarith
  have hexp : |(a : ℝ) * b * c| ≤ 2 ^ 4 * max (exp (h1 ε / 2)) (r ^ (3 * (1 + ε))) := by
    calc |(a : ℝ) * b * c| = exp (Real.log |(a : ℝ) * b * c|) := (exp_log hX).symm
      _ ≤ exp (4 * Real.log 2 + max ((3 * (1 + ε)) * Real.log r) (h1 ε / 2)) := exp_le_exp.mpr hlog
      _ = 2 ^ 4 * max (exp (h1 ε / 2)) (r ^ (3 * (1 + ε))) := by
          rw [exp_add, rpow_def_of_pos hr0, Real.exp_monotone.map_max, max_comm,
            show (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) by rw [Real.log_pow]; norm_num,
            exp_log (by norm_num)]
          ring_nf
  have hEm : 1 ≤ exp (h1 ε / 2) := one_le_exp (by positivity)
  have hr1 : 1 ≤ r := le_trans hR1 hRr
  have hRm : 1 ≤ r ^ (3 * (1 + ε)) := one_le_rpow hr1 (by positivity)
  rw [← hh]
  refine ⟨?_, ?_⟩
  · push_cast
    exact hexp
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le_mul_of_one_le hEm hRm) (by positivity)

end ExpEst
