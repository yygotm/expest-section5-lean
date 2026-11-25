import ExpEst.Lemma57

/-!
# ExpEst Corollary 5.8

Assuming Theorem 5.3 (ii) of the paper for `L = ℚ`, `ε = 1`, there is no solution of
`x^p + y^p = z^p` in positive integers for primes `p > 1.615 · 10^14`.

## The hypothesis

Theorem 5.3 (ii), first inequality, for `L = ℚ` (so `d = 1`, `Δ_ℚ = 1`) and `ε = 1`, reads

  `H_ℚ(a, b, c) ≤ 2^(5/2) · max{exp(h₁(1)/4), rad_ℚ(a, b, c)^3}`

for nonzero `a, b, c ∈ ℚ` with `a + b + c = 0`, where `h₁(ε) = 3.4·10^30·ε^(-166/81)`.
Both sides are unchanged under `(a, b, c) ↦ (λa, λb, λc)`, `λ ∈ ℚ^×`, so it suffices to state
it for coprime integers; for those `H_ℚ(a, b, c) = max{|a|, |b|, |c|}` and
`rad_ℚ(a, b, c) = rad(abc)` (product of the primes dividing `abc`).
This integral form is `Thm53ii_Q_int`.  (The scaling reduction and the two identifications
are not formalized in this file; `Thm53.lean` derives the integral form from the rational
form `Thm53ii_Q`, and `L2.lean` proves the primitive representative and the height bounds.)

The paper's proof of Corollary 5.8 uses the weaker product form
`H ≤ 2^(5/2) · exp(h₁(1)/4) · rad^3`, which follows from the max form
(`max_le_mul_of_one_le`).
-/

namespace ExpEst

open Real

/-- `h₁(ε) = 3.4·10^30·ε^(-166/81)` (Theorem 5.3, `d = 1`); for positive `ε` it is `≥ 3.4·10^30` iff `ε ≤ 1`. -/
noncomputable def h1 (ε : ℝ) : ℝ := 3.4 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81)

theorem h1_one : h1 1 = 3.4 * 10 ^ 30 := by simp [h1]

/-- Radical of a nonzero integer: the product of the distinct primes dividing it
(Lean gives `rad 0 = 1`; the main theorems never need this value). -/
def rad (n : ℤ) : ℕ := ∏ q ∈ n.natAbs.primeFactors, q

/-- Theorem 5.3 (ii) of the paper for `L = ℚ`, `ε = 1`, stated for coprime integers. -/
def Thm53ii_Q_int : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 → IsCoprime a b →
    (max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|)) ≤
      2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) ((rad (a * b * c) : ℝ) ^ 3)

theorem max_le_mul_of_one_le {E R : ℝ} (hE : 1 ≤ E) (hR : 1 ≤ R) : max E R ≤ E * R :=
  max_le (le_mul_of_one_le_right (by linarith) hR) (le_mul_of_one_le_left (by linarith) hE)

/-- `rad(x^p y^p (-z^p)) ≤ x y z` for positive integers. -/
theorem rad_fermat_le {p : ℕ} (hp0 : p ≠ 0) {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (rad (x ^ p * y ^ p * (-z ^ p)) : ℤ) ≤ x * y * z := by
  have hn : (x ^ p * y ^ p * (-z ^ p)).natAbs = (x * y * z).natAbs ^ p := by
    simp [Int.natAbs_mul, Int.natAbs_pow, mul_pow]
  have hxyz : (0 : ℤ) < x * y * z := by positivity
  rw [rad, hn, Nat.primeFactors_pow _ hp0]
  have h1 := Nat.le_of_dvd (Int.natAbs_pos.mpr hxyz.ne') (Nat.prod_primeFactors_dvd _)
  have h2 : ((x * y * z).natAbs : ℤ) = x * y * z := Int.natAbs_of_nonneg hxyz.le
  calc ((∏ q ∈ (x * y * z).natAbs.primeFactors, q : ℕ) : ℤ) ≤ ((x * y * z).natAbs : ℤ) := by
        exact_mod_cast h1
    _ = x * y * z := h2

/-- `log(1.615·10^14) ≥ 32.7`, via `1.615·10^14 = 2^47 · 1.1475…` and `log 2 > 0.6931471803`. -/
theorem log_P0_ge : (32.7 : ℝ) ≤ log (1.615 * 10 ^ 14) := by
  have hsplit : log (1.615 * 10 ^ 14) = 47 * log 2 + log ((1.615 * 10 ^ 14) / 2 ^ 47) := by
    rw [log_div (by norm_num) (by norm_num), log_pow]
    push_cast
    ring
  have h2 := log_two_gt_d9
  have h3 := one_sub_inv_le_log_of_pos (x := (1.615 * 10 ^ 14 : ℝ) / 2 ^ 47) (by norm_num)
  norm_num at h3
  rw [hsplit]
  norm_num at h2 ⊢
  linarith


/-- Paper, proof of Cor 5.8: `5/2 + log₂(e) · h₁(1)/4 < 1.227·10^30`. -/
theorem cor58_numeric_upper : (5 : ℝ) / 2 + (h1 1 / 4) / log 2 < 1.227 * 10 ^ 30 := by
  rw [h1_one]
  have h2 := log_two_gt_d9
  have hl : 0 < log 2 := by linarith
  have key : (3.4 * 10 ^ 30 / 4 : ℝ) / log 2 < 1.227 * 10 ^ 30 - 5 / 2 := by
    rw [div_lt_iff₀ hl]
    norm_num at h2 ⊢
    linarith
  linarith

/-- Paper, proof of Cor 5.8: for `P > 1.615·10^14`,
`(P - 9)(-1 + P · log₂(P + 1)) > 1.227·10^30`.  The paper argues via `1/log 2 > 1.44` and the
monotonicity of `(x - 9)(-1 + 1.44 x log(x + 1))` on `x ≥ 9`; we use the same constant `1.44`
and bound each (positive, increasing) factor at `P₀ = 1.615·10^14`. -/
theorem cor58_numeric_lower {P : ℝ} (hP : 1.615 * 10 ^ 14 < P) :
    1.227 * 10 ^ 30 < (P - 9) * (-1 + P * log (P + 1) / log 2) := by
  have h2 := log_two_lt_d9
  have h2' := log_two_gt_d9
  have hl : 0 < log 2 := by linarith
  have hL : (32.7 : ℝ) ≤ log (P + 1) :=
    le_trans log_P0_ge (log_le_log (by norm_num) (by linarith))
  have hPL : (1.615 * 10 ^ 14 : ℝ) * 32.7 ≤ P * log (P + 1) :=
    mul_le_mul hP.le hL (by norm_num) (by linarith)
  have hX0 : 0 ≤ P * log (P + 1) := by linarith
  have h144 : 1.44 * (P * log (P + 1)) ≤ P * log (P + 1) / log 2 := by
    rw [le_div_iff₀ hl]
    nlinarith [mul_nonneg hX0 (sub_nonneg.mpr h2.le)]
  calc (1.227 * 10 ^ 30 : ℝ)
      < (1.615 * 10 ^ 14 - 9) * (-1 + 1.44 * (1.615 * 10 ^ 14 * 32.7)) := by norm_num
    _ ≤ (P - 9) * (-1 + 1.44 * (P * log (P + 1))) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    _ ≤ (P - 9) * (-1 + P * log (P + 1) / log 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- Corollary 5.8 for a coprime solution. -/
theorem cor58_coprime (H : Thm53ii_Q_int) {p : ℕ} (hp : p.Prime)
    (hpbig : (1.615 * 10 ^ 14 : ℝ) < p) {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : IsCoprime x y) (h : x ^ p + y ^ p = z ^ p) : False := by
  have hp9 : 9 ≤ p := by
    have : (9 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hp10 : 10 ≤ p := by
    have : (10 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hp3 : 3 ≤ p := by omega
  have hp0 : p ≠ 0 := by omega
  have h57 := lemma57 hp hp3 hx hy hz hxy h
  obtain ⟨hzx, hzy⟩ := lt_z_of_fermat hp hx hy hz h
  -- apply Theorem 5.3 (ii) to (x^p, y^p, -z^p)
  have hH := H (x ^ p) (y ^ p) (-z ^ p) (pow_ne_zero _ hx.ne') (pow_ne_zero _ hy.ne')
    (neg_ne_zero.mpr (pow_ne_zero _ hz.ne')) (by linarith) hxy.pow
  have hZ1 : (1 : ℝ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  have hZ0 : (0 : ℝ) ≤ z := by linarith
  have hlhs : (z : ℝ) ^ p ≤ max |((x ^ p : ℤ) : ℝ)| (max |((y ^ p : ℤ) : ℝ)| |((-z ^ p : ℤ) : ℝ)|) := by
    apply le_max_of_le_right
    apply le_max_of_le_right
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  -- rad(x^p y^p z^p) ≤ xyz ≤ z^3
  set R : ℕ := rad (x ^ p * y ^ p * (-z ^ p)) with hRdef
  have hrad : (R : ℝ) ≤ (z : ℝ) ^ 3 := by
    have h1 := rad_fermat_le hp0 hx hy hz
    have h2 : x * y * z ≤ z ^ 3 := by
      have : x * y ≤ z * z := mul_le_mul hzx.le hzy.le hy.le hz.le
      nlinarith
    exact_mod_cast h1.trans h2
  have hR1 : (1 : ℝ) ≤ (R : ℝ) ^ 3 := by
    have : 1 ≤ R := by
      rw [hRdef, rad]
      exact Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
    exact one_le_pow₀ (by exact_mod_cast this)
  have hE1 : (1 : ℝ) ≤ exp (h1 1 / 4) := one_le_exp (by rw [h1_one]; positivity)
  set C : ℝ := 2 ^ ((5 : ℝ) / 2) * exp (h1 1 / 4) with hCdef
  have hmain : (z : ℝ) ^ p ≤ C * (z : ℝ) ^ 9 := by
    have h5 : (0 : ℝ) ≤ 2 ^ ((5 : ℝ) / 2) := by positivity
    calc (z : ℝ) ^ p ≤ _ := hlhs.trans hH
      _ ≤ 2 ^ ((5 : ℝ) / 2) * (exp (h1 1 / 4) * (R : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (max_le_mul_of_one_le hE1 hR1) h5
      _ ≤ 2 ^ ((5 : ℝ) / 2) * (exp (h1 1 / 4) * ((z : ℝ) ^ 3) ^ 3) := by
          gcongr
      _ = C * (z : ℝ) ^ 9 := by rw [hCdef]; ring
  -- z^(p-9) ≤ C
  have hZp : (z : ℝ) ^ p = (z : ℝ) ^ (p - 9) * (z : ℝ) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  have hC : (z : ℝ) ^ (p - 9) ≤ C := by
    rw [hZp] at hmain
    exact le_of_mul_le_mul_right hmain (by positivity)
  -- z > (p + 1)^p / 2 (Lemma 5.7)
  have hZlow : ((p : ℝ) + 1) ^ p / 2 < z := by
    have : ((((p : ℤ) + 1) ^ p : ℤ) : ℝ) < ((2 * z : ℤ) : ℝ) := by exact_mod_cast h57
    push_cast at this
    linarith
  have hlt : (((p : ℝ) + 1) ^ p / 2) ^ (p - 9) < C :=
    lt_of_lt_of_le (pow_lt_pow_left₀ hZlow (by positivity) (by omega)) hC
  -- take logarithms
  have hlog := log_lt_log (by positivity) hlt
  rw [log_pow, log_div (by positivity) (by norm_num), log_pow, hCdef,
    log_mul (by positivity) (by positivity), log_rpow (by norm_num), log_exp,
    Nat.cast_sub hp9] at hlog
  push_cast at hlog
  -- hlog : (p - 9) * (p * log (p + 1) - log 2) < 5/2 * log 2 + h₁(1)/4
  have hl : 0 < log 2 := by linarith [log_two_gt_d9]
  have hX : ((p : ℝ) - 9) * (-1 + (p : ℝ) * log ((p : ℝ) + 1) / log 2) <
      5 / 2 + (h1 1 / 4) / log 2 := by
    have e1 : ((p : ℝ) - 9) * (-1 + (p : ℝ) * log ((p : ℝ) + 1) / log 2) =
        (((p : ℝ) - 9) * ((p : ℝ) * log ((p : ℝ) + 1) - log 2)) / log 2 := by
      field_simp
      ring
    have e2 : (5 / 2 + (h1 1 / 4) / log 2 : ℝ) = (5 / 2 * log 2 + h1 1 / 4) / log 2 := by
      field_simp
    rw [e1, e2]
    exact div_lt_div_of_pos_right hlog hl
  linarith [cor58_numeric_upper, cor58_numeric_lower hpbig]

/-- **Corollary 5.8.** Assume Theorem 5.3 (ii) for `L = ℚ`, `ε = 1`. If `p > 1.615·10^14` is
prime, then `x^p + y^p = z^p` has no solution in positive integers. -/
theorem cor58 (H : Thm53ii_Q_int) {p : ℕ} (hp : p.Prime) (hpbig : (1.615 * 10 ^ 14 : ℝ) < p)
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ p + y ^ p ≠ z ^ p := by
  intro h
  have hp0 : p ≠ 0 := hp.ne_zero
  have hg : 0 < Int.gcd x y := Int.gcd_pos_of_ne_zero_left _ hx.ne'
  obtain ⟨g, x', y', hg0, hgcd, rfl, rfl⟩ := Int.exists_gcd_one' hg
  have hg0' : (0 : ℤ) < g := by exact_mod_cast hg0
  have hgz : (g : ℤ) ∣ z := by
    have : (g : ℤ) ^ p ∣ z ^ p := ⟨x' ^ p + y' ^ p, by rw [← h]; ring⟩
    exact (Int.pow_dvd_pow_iff hp0).mp this
  obtain ⟨z', rfl⟩ := hgz
  have hx' : 0 < x' := pos_of_mul_pos_left hx hg0'.le
  have hy' : 0 < y' := pos_of_mul_pos_left hy hg0'.le
  have hz' : 0 < z' := pos_of_mul_pos_right hz hg0'.le
  have h' : x' ^ p + y' ^ p = z' ^ p := by
    apply mul_left_cancel₀ (pow_ne_zero p hg0'.ne')
    linear_combination h
  exact cor58_coprime H hp hpbig hx' hy' hz' (Int.isCoprime_iff_gcd_eq_one.mpr hgcd) h'

end ExpEst
