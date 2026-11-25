import ExpEst.Cor58
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# L3, numeric part: Claims 5.2A, 5.2B and (P8) of Corollary 5.2 (`d = 1`)

Notation of the paper (pp. 35–43): `δ = 2^12·3^3·5·d = 552960` for `d = 1`,
`h = log(𝔮^∀)`, `L(h) = log(1.45·δ·h)`.  We write `h^{-1/2}·X` as `X / √h`.
-/

namespace ExpEst

open Real

/-- `δ = 2^12·3^3·5·d` for `d = 1` (Corollary 5.2). -/
def δ₁ : ℝ := 552960

theorem δ₁_eq : δ₁ = 2 ^ 12 * 3 ^ 3 * 5 := by norm_num [δ₁]

/-- `log y ≤ n·log 2 + (y / 2^n - 1)`. -/
theorem log_le_two_pow (y : ℝ) (hy : 0 < y) (n : ℕ) :
    Real.log y ≤ n * Real.log 2 + (y / 2 ^ n - 1) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hyy : y = 2 ^ n * (y / 2 ^ n) := by field_simp
  have := Real.log_le_sub_one_of_pos (div_pos hy h2)
  calc Real.log y = Real.log (2 ^ n) + Real.log (y / 2 ^ n) := by
        rw [← Real.log_mul h2.ne' (div_pos hy h2).ne', ← hyy]
    _ ≤ n * Real.log 2 + (y / 2 ^ n - 1) := by rw [Real.log_pow]; linarith

/-- `n·log 2 ≤ log y` when `2^n ≤ y`. -/
theorem two_pow_le_log (y : ℝ) (n : ℕ) (hy : (2 : ℝ) ^ n ≤ y) : n * Real.log 2 ≤ Real.log y := by
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) hy

/-- `L₁ = log(1.45·δ·h₁(1))` lies in `[83, 83.9]` (the paper uses `≥ 83`, p. 41). -/
theorem L1_bounds : 83 ≤ Real.log (1.45 * δ₁ * (3.4 * 10 ^ 30)) ∧
    Real.log (1.45 * δ₁ * (3.4 * 10 ^ 30)) ≤ 83.9 := by
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  constructor
  · have := two_pow_le_log (1.45 * δ₁ * (3.4 * 10 ^ 30)) 121 (by norm_num [δ₁])
    push_cast at this
    linarith
  · have := log_le_two_pow (1.45 * δ₁ * (3.4 * 10 ^ 30)) (by norm_num [δ₁]) 121
    push_cast at this
    norm_num [δ₁] at this ⊢
    linarith

/-- `√(3.4·10^30) ≥ 1.8439·10^15`. -/
theorem sqrt_h1_ge : (1.8439 * 10 ^ 15 : ℝ) ≤ √(3.4 * 10 ^ 30) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- The constant of Claim 5.2A at `ε = 1`:
`71.82·δ²·h₁(1)^{-1/2}·log(1.45·δ·h₁(1)) ≤ 1 - 10^{-7}` (p. 41, "one verifies easily"). -/
theorem K1_le : 71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * (3.4 * 10 ^ 30)) / √(3.4 * 10 ^ 30)
    ≤ 1 - 10 ^ (-7 : ℤ) := by
  have hL := L1_bounds.2
  have hs := sqrt_h1_ge
  have hs0 : (0 : ℝ) < √(3.4 * 10 ^ 30) := by positivity
  rw [div_le_iff₀ hs0]
  have hδ : (0 : ℝ) ≤ 71.82 * δ₁ ^ 2 := by norm_num [δ₁]
  calc 71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * (3.4 * 10 ^ 30))
      ≤ 71.82 * δ₁ ^ 2 * 83.9 := mul_le_mul_of_nonneg_left hL hδ
    _ ≤ (1 - 10 ^ (-7 : ℤ)) * (1.8439 * 10 ^ 15) := by norm_num [δ₁]
    _ ≤ (1 - 10 ^ (-7 : ℤ)) * √(3.4 * 10 ^ 30) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)

/-- Monotonicity used in Claim 5.2A (p. 41): `x ↦ x^{-1/2}·log(c·x)` is decreasing
where `log(c·x) ≥ 2`.  Stated as: if `0 < H ≤ h` and `log(c·H) ≥ 2`, then
`log(c·h)/√h ≤ log(c·H)/√H`. -/
theorem log_div_sqrt_antitone {c H h : ℝ} (hc : 0 < c) (hH : 0 < H) (hHh : H ≤ h)
    (hL : 2 ≤ Real.log (c * H)) : Real.log (c * h) / √h ≤ Real.log (c * H) / √H := by
  set s := h / H with hs_def
  have hs1 : 1 ≤ s := by rw [hs_def, le_div_iff₀ hH]; linarith
  have hs0 : 0 < s := by linarith
  have hh : h = H * s := by rw [hs_def]; field_simp
  have hsq : √h = √H * √s := by rw [hh, Real.sqrt_mul hH.le]
  have hlog : Real.log (c * h) = Real.log (c * H) + Real.log s := by
    rw [hh, ← mul_assoc, Real.log_mul (by positivity) hs0.ne']
  have hrs : 1 ≤ √s := by rw [Real.one_le_sqrt]; exact hs1
  have hlogs : Real.log s ≤ 2 * (√s - 1) := by
    have h1 : Real.log √s = Real.log s / 2 := Real.log_sqrt hs0.le
    have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hs0)
    linarith
  have hH' : 0 < √H := Real.sqrt_pos.mpr hH
  have hs' : 0 < √s := by linarith
  rw [hsq, hlog, div_le_div_iff₀ (mul_pos hH' hs') hH']
  have key : Real.log (c * H) + Real.log s ≤ Real.log (c * H) * √s := by nlinarith
  calc (Real.log (c * H) + Real.log s) * √H ≤ (Real.log (c * H) * √s) * √H :=
        mul_le_mul_of_nonneg_right key hH'.le
    _ = Real.log (c * H) * (√H * √s) := by ring

/-- `t·(1 - log t) ≤ 1` for `t > 0` (p. 41). -/
theorem mul_one_sub_log_le_one {t : ℝ} (ht : 0 < t) : t * (1 - Real.log t) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h
  have : t * (-Real.log t) ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left h ht.le
  rw [mul_sub, mul_inv_cancel₀ ht.ne'] at this
  linarith

/-- With `u = ε^{1/81}`: `ε = u^81` and `h₁(ε) = 3.4·10^30 / u^166`. -/
theorem h1_eq_u {ε : ℝ} (hε : 0 < ε) :
    ε = (ε ^ ((1 : ℝ) / 81)) ^ 81 ∧ h1 ε = 3.4 * 10 ^ 30 / (ε ^ ((1 : ℝ) / 81)) ^ 166 := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  · have e1 : ε ^ (-(166 : ℝ) / 81) = (ε ^ ((1 : ℝ) / 81)) ^ (-(166 : ℝ)) := by
      rw [← Real.rpow_mul hε.le]; norm_num
    rw [h1, e1, Real.rpow_neg (by positivity), show (166 : ℝ) = ((166 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, div_eq_mul_inv]
    rfl

/-- **Claim 5.2A** (`d = 1`, p. 41): if `0 < ε ≤ 1` and `h ≥ h₁(ε)`, then
`71.82·δ²·h^{-1/2}·log(1.45·δ·h) ≤ ε·(1 - 10^{-7})`. -/
theorem claim52A {ε h : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : h1 ε ≤ h) :
    71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * h) / √h ≤ ε * (1 - 10 ^ (-7 : ℤ)) := by
  obtain ⟨hεu, hHu⟩ := h1_eq_u hε
  set u := ε ^ ((1 : ℝ) / 81) with hu_def
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  set H := h1 ε with hH_def
  set L1 := Real.log (1.45 * δ₁ * (3.4 * 10 ^ 30)) with hL1
  set s1 := √(3.4 * 10 ^ 30 : ℝ) with hs1
  have hL1b := L1_bounds
  have hK1 := K1_le
  have hs10 : 0 < s1 := by positivity
  have hu166 : 0 < u ^ 166 := by positivity
  have hH0 : 0 < H := by rw [hHu]; positivity
  have hlogH : Real.log (1.45 * δ₁ * H) = L1 - 166 * Real.log u := by
    rw [hHu, mul_div_assoc', Real.log_div (by norm_num [δ₁]) hu166.ne', Real.log_pow]
    push_cast; ring
  have hsqrtH : √H = s1 / u ^ 83 := by
    rw [hHu, Real.sqrt_div' _ hu166.le, show u ^ 166 = (u ^ 83) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hmono := log_div_sqrt_antitone (c := 1.45 * δ₁) (by norm_num [δ₁]) hH0 hh
    (by rw [hlogH]; nlinarith)
  have hA : (0 : ℝ) ≤ 71.82 * δ₁ ^ 2 := by norm_num [δ₁]
  have hstep1 : 71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * h) / √h
      ≤ 71.82 * δ₁ ^ 2 * (Real.log (1.45 * δ₁ * H) / √H) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hmono hA
  have ht := mul_one_sub_log_le_one (pow_pos hu0 2)
  rw [Real.log_pow] at ht
  push_cast at ht
  have hK1' : 71.82 * δ₁ ^ 2 * L1 / s1 ≤ 1 - 10 ^ (-7 : ℤ) := hK1
  have hK0 : 0 ≤ 71.82 * δ₁ ^ 2 * L1 / s1 := by
    apply div_nonneg _ hs10.le; nlinarith
  have hu81 : 0 < u ^ 81 := by positivity
  calc 71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * h) / √h
      ≤ 71.82 * δ₁ ^ 2 * (Real.log (1.45 * δ₁ * H) / √H) := hstep1
    _ = 71.82 * δ₁ ^ 2 * L1 / s1 * u ^ 81 * (u ^ 2 * (1 - 166 / L1 * Real.log u)) := by
        rw [hlogH, hsqrtH]
        have : L1 ≠ 0 := by linarith
        field_simp
    _ ≤ 71.82 * δ₁ ^ 2 * L1 / s1 * u ^ 81 * (u ^ 2 * (1 - 2 * Real.log u)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 166 / L1 ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        nlinarith
    _ ≤ 71.82 * δ₁ ^ 2 * L1 / s1 * u ^ 81 * 1 :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (1 - 10 ^ (-7 : ℤ)) * u ^ 81 := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right hK1' hu81.le
    _ = ε * (1 - 10 ^ (-7 : ℤ)) := by rw [← hεu]; ring

/-- `h ≥ h₁(ε)` with `0 < ε ≤ 1` gives `h ≥ 3.4·10^30` (`h₁(ε) ≥ h₁(1)`). -/
theorem le_of_h1_le {ε h : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : h1 ε ≤ h) :
    (3.4 * 10 ^ 30 : ℝ) ≤ h := by
  obtain ⟨-, hHu⟩ := h1_eq_u hε
  have hu0 : 0 < ε ^ ((1 : ℝ) / 81) := by positivity
  have hu1 : ε ^ ((1 : ℝ) / 81) ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hp : 0 < (ε ^ ((1 : ℝ) / 81)) ^ 166 := by positivity
  have hp1 : (ε ^ ((1 : ℝ) / 81)) ^ 166 ≤ 1 := pow_le_one₀ hu0.le hu1
  have : (3.4 * 10 ^ 30 : ℝ) ≤ h1 ε := by
    rw [hHu, le_div_iff₀ hp]; nlinarith
  linarith

/-- `√h ≥ 10^15` when `h ≥ 10^30`. -/
theorem sqrt_ge_of_ge {h : ℝ} (hh : (10 : ℝ) ^ 30 ≤ h) : (10 : ℝ) ^ 15 ≤ √h := by
  rw [Real.le_sqrt (by norm_num) (by linarith)]; norm_num at hh ⊢; linarith

/-- `log(1.45·δ·h) ≥ 3` when `h ≥ 1`. -/
theorem L_ge_three {h : ℝ} (hh : 1 ≤ h) : 3 ≤ Real.log (1.45 * δ₁ * h) := by
  have := two_pow_le_log (1.45 * δ₁ * h) 5 (by norm_num [δ₁]; nlinarith)
  have l2 := Real.log_two_gt_d9
  push_cast at this; linarith

/-- **Claim 5.2B** (`d = 1`, p. 42): if `0 < ε ≤ 1`, `h ≥ h₁(ε)` and `l` satisfies (P1)
`h^{1/2} ≤ l ≤ 1.464·δ·h^{1/2}·log(1.45·δ·h)`, then
`2·h^{-1/2}·log l + 71.82·δ²·h^{-1/2}·log(1.45·δ·h) + δ·h^{-1/2} ≤ ε`. -/
theorem claim52B {ε h l : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : h1 ε ≤ h)
    (hl1 : √h ≤ l) (hl2 : l ≤ 1.464 * δ₁ * √h * Real.log (1.45 * δ₁ * h)) :
    2 * Real.log l / √h + 71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * h) / √h + δ₁ / √h ≤ ε := by
  have hA := claim52A hε hε1 hh
  have h34 := le_of_h1_le hε hε1 hh
  have hh0 : 0 < h := by linarith
  have hr := sqrt_ge_of_ge (h := h) (by linarith)
  set r := √h with hr_def
  have hr0 : 0 < r := by linarith
  have hrr : r * r = h := Real.mul_self_sqrt hh0.le
  set L := Real.log (1.45 * δ₁ * h) with hL_def
  have hL3 : 3 ≤ L := L_ge_three (by linarith)
  have hLle : L ≤ 1.45 * δ₁ * h := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1.45 * δ₁ * h by norm_num [δ₁]; linarith)
    linarith
  have hl0 : 0 < l := by linarith
  have hδ : (0 : ℝ) < δ₁ := by norm_num [δ₁]
  -- `l ≤ (1.45·δ·h)^2`, hence `log l ≤ 2·L`
  have hlsq : l ≤ (1.45 * δ₁ * h) ^ 2 := by
    calc l ≤ 1.464 * δ₁ * r * L := hl2
      _ ≤ 1.464 * δ₁ * r * (1.45 * δ₁ * h) := by
          apply mul_le_mul_of_nonneg_left hLle; positivity
      _ ≤ (1.45 * r) * δ₁ * r * (1.45 * δ₁ * h) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hr0.le
          apply mul_le_mul_of_nonneg_right _ hδ.le
          linarith
      _ = (1.45 * δ₁ * h) ^ 2 := by rw [← hrr]; ring
  have hlogl : Real.log l ≤ 2 * L := by
    have := Real.log_le_log hl0 hlsq
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  set K := 71.82 * δ₁ ^ 2 * L / r with hK
  have hnum : 2 * Real.log l + 71.82 * δ₁ ^ 2 * L + δ₁
      ≤ (1 + 10 ^ (-12 : ℤ) + 10 ^ (-8 : ℤ)) * (71.82 * δ₁ ^ 2 * L) := by
    norm_num [δ₁] at hL3 hlogl ⊢; nlinarith
  calc 2 * Real.log l / r + 71.82 * δ₁ ^ 2 * L / r + δ₁ / r
      = (2 * Real.log l + 71.82 * δ₁ ^ 2 * L + δ₁) / r := by ring
    _ ≤ (1 + 10 ^ (-12 : ℤ) + 10 ^ (-8 : ℤ)) * (71.82 * δ₁ ^ 2 * L) / r :=
        div_le_div_of_nonneg_right hnum hr0.le
    _ = (1 + 10 ^ (-12 : ℤ) + 10 ^ (-8 : ℤ)) * K := by rw [hK]; ring
    _ ≤ (1 + 10 ^ (-12 : ℤ) + 10 ^ (-8 : ℤ)) * (ε * (1 - 10 ^ (-7 : ℤ))) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
    _ ≤ ε := by
        have : (1 + 10 ^ (-12 : ℤ) + 10 ^ (-8 : ℤ)) * (1 - 10 ^ (-7 : ℤ)) ≤ (1 : ℝ) := by norm_num
        nlinarith

/-- From Theorem 5.1's inequality to the display before (P8) (pp. 40–41).  Inputs: Theorem 5.1
`(1/6)·log 𝔮 ≤ (1 + 20·d_mod/l)·D + 4.0881·e*_mod·l` (with `D = log 𝔡^{F_tpd} + log 𝔣^{F_tpd}`),
the consequence `h - log 𝔮 ≤ h^{1/2}·log l` of (P3), (P1), and `20·d_mod ≤ δ`, `e*_mod ≤ δ`. -/
theorem thm51_eval {h l D dmod emod logq : ℝ} (hh0 : 0 < h) (hl1 : √h ≤ l)
    (hl2 : l ≤ 1.464 * δ₁ * √h * Real.log (1.45 * δ₁ * h)) (hD : 0 ≤ D) (hd0 : 0 ≤ dmod)
    (hd : 20 * dmod ≤ δ₁) (he : emod ≤ δ₁)
    (h51 : logq / 6 ≤ (1 + 20 * dmod / l) * D + 4.0881 * emod * l)
    (hP3 : h - logq ≤ √h * Real.log l) :
    h / 6 ≤ (1 + δ₁ / √h) * D + √h * Real.log l / 6
      + 5.985 * δ₁ ^ 2 * √h * Real.log (1.45 * δ₁ * h) := by
  have hr0 : 0 < √h := Real.sqrt_pos.mpr hh0
  have hl0 : 0 < l := by linarith
  set L := Real.log (1.45 * δ₁ * h)
  have hδ : (0 : ℝ) < δ₁ := by norm_num [δ₁]
  have hL0 : 0 ≤ L := by
    by_contra hneg
    push Not at hneg
    have : 1.464 * δ₁ * √h * L < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have h1 : 20 * dmod / l ≤ δ₁ / √h := by
    rw [div_le_div_iff₀ hl0 hr0]; nlinarith
  have h2 : (1 + 20 * dmod / l) * D ≤ (1 + δ₁ / √h) * D := by
    apply mul_le_mul_of_nonneg_right _ hD; linarith
  have h3 : 4.0881 * emod * l ≤ 5.985 * δ₁ ^ 2 * √h * L := by
    have hrL : 0 ≤ √h * L := mul_nonneg hr0.le hL0
    calc 4.0881 * emod * l ≤ 4.0881 * δ₁ * (1.464 * δ₁ * √h * L) := by
          apply mul_le_mul (by linarith) hl2 hl0.le (by positivity)
      _ = 5.9849784 * δ₁ ^ 2 * (√h * L) := by ring
      _ ≤ 5.985 * δ₁ ^ 2 * (√h * L) := by
          apply mul_le_mul_of_nonneg_right _ hrL; nlinarith
      _ = 5.985 * δ₁ ^ 2 * √h * L := by ring
  linarith

/-- (P8) and the end of the proof of (C2) (pp. 41, 43): from the display before (P8) and
Claim 5.2B, `(1/6)·h ≤ (1 + ε)·D`.  Uses `(1 - x)^{-1}·(1 + y) ≤ 1 + ε` for
`x, y ≥ 0`, `2x + y ≤ ε ≤ 1`. -/
theorem c2_of_p8 {ε h l D : ℝ} (hε1 : ε ≤ 1) (hh0 : 0 < h) (hl1 : 1 ≤ l) (hD : 0 ≤ D)
    (hL0 : 0 ≤ Real.log (1.45 * δ₁ * h))
    (hT : h / 6 ≤ (1 + δ₁ / √h) * D + √h * Real.log l / 6
      + 5.985 * δ₁ ^ 2 * √h * Real.log (1.45 * δ₁ * h))
    (hB : 2 * Real.log l / √h + 71.82 * δ₁ ^ 2 * Real.log (1.45 * δ₁ * h) / √h + δ₁ / √h ≤ ε) :
    h / 6 ≤ (1 + ε) * D := by
  set r := √h with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hh0
  have hrr : r * r = h := Real.mul_self_sqrt hh0.le
  set L := Real.log (1.45 * δ₁ * h)
  have hlog0 : 0 ≤ Real.log l := Real.log_nonneg hl1
  set x := Real.log l / r + 35.91 * δ₁ ^ 2 * L / r with hx
  set y := δ₁ / r with hy
  have hδ : (0 : ℝ) < δ₁ := by norm_num [δ₁]
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hxy : 2 * x + y ≤ ε := by
    have : 2 * x + y = 2 * Real.log l / r + 71.82 * δ₁ ^ 2 * L / r + δ₁ / r := by
      rw [hx, hy]; ring
    linarith
  have hxr : x * r = Real.log l + 35.91 * δ₁ ^ 2 * L := by
    rw [hx]; field_simp
  -- (P8): `(1/6)·h·(1 - x) ≤ (1 + y)·D`
  have hP8 : h / 6 * (1 - x) ≤ (1 + y) * D := by
    have e : h / 6 * (1 - x) = h / 6 - r * (x * r) / 6 := by rw [← hrr]; ring
    rw [e, hxr]
    have e2 : r * (Real.log l + 35.91 * δ₁ ^ 2 * L) / 6
        = r * Real.log l / 6 + 5.985 * δ₁ ^ 2 * r * L := by ring
    rw [e2]; linarith
  have h1x : 0 < 1 - x := by linarith
  have hkey : 1 + y ≤ (1 + ε) * (1 - x) := by nlinarith
  have : h / 6 * (1 - x) ≤ (1 + ε) * D * (1 - x) := by
    calc h / 6 * (1 - x) ≤ (1 + y) * D := hP8
      _ ≤ (1 + ε) * (1 - x) * D := mul_le_mul_of_nonneg_right hkey hD
      _ = (1 + ε) * D * (1 - x) := by ring
  exact le_of_mul_le_mul_right this h1x

/-- The numeric core of (P5) (pp. 39–40): if `h ≥ 10^30` and
`0 < l ≤ 1.464·δ·h^{1/2}·log(1.45·δ·h)`, then `log l < h^{1/2}`
(the paper: `f(h) > 0` for `f(x) = x^{1/2} - 1.5·log x - 2·log(2δ)`). -/
theorem log_l_lt_sqrt {h l : ℝ} (hh : (10 : ℝ) ^ 30 ≤ h) (hl0 : 0 < l)
    (hl2 : l ≤ 1.464 * δ₁ * √h * Real.log (1.45 * δ₁ * h)) : Real.log l < √h := by
  have hh0 : 0 < h := by linarith
  have hs := sqrt_ge_of_ge hh
  set s := √h with hs_def
  have hss : s * s = h := Real.mul_self_sqrt hh0.le
  have hδ : (0 : ℝ) < δ₁ := by norm_num [δ₁]
  have hLle : Real.log (1.45 * δ₁ * h) ≤ 1.45 * δ₁ * h := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1.45 * δ₁ * h by positivity)
    linarith
  set c : ℝ := 1.464 * 1.45 * δ₁ ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hs0 : 0 < s := by linarith
  have hlc : l ≤ c * s ^ 3 := by
    calc l ≤ 1.464 * δ₁ * s * Real.log (1.45 * δ₁ * h) := hl2
      _ ≤ 1.464 * δ₁ * s * (1.45 * δ₁ * h) := by
          apply mul_le_mul_of_nonneg_left hLle; positivity
      _ = c * s ^ 3 := by rw [hc, ← hss]; ring
  have hlog : Real.log l ≤ Real.log c + 3 * Real.log s := by
    have := Real.log_le_log hl0 hlc
    rwa [Real.log_mul hc0.ne' (by positivity), Real.log_pow, Nat.cast_ofNat] at this
  have hlc' : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  have hcval : c ≤ 10 ^ 12 := by rw [hc]; norm_num [δ₁]
  set w := √s with hw
  have hw0 : 0 < w := Real.sqrt_pos.mpr hs0
  have hww : w * w = s := Real.mul_self_sqrt hs0.le
  have hlogs : Real.log s ≤ 2 * w := by
    have h1 : Real.log w = Real.log s / 2 := Real.log_sqrt hs0.le
    have h2 := Real.log_le_sub_one_of_pos hw0
    linarith
  have hw12 : 12 ≤ w := by nlinarith
  nlinarith

end ExpEst
