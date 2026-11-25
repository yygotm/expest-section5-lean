import ExpEstL2
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ExpEstL3
open Real ExpEstL2
noncomputable section

abbrev δ : ℝ := 552960
abbrev scale : ℝ := 1.45 * δ
abbrev baseH : ℝ := 3.4 * 10^30

private theorem log_base_lower : 82.65 ≤ log (scale * 10^30) := by
  let z : ℝ := (scale * 10^30) / 2^119
  have hz : 0 < z := by norm_num [z, scale, δ]
  have h := one_sub_inv_le_log_of_pos hz
  have he : scale * 10^30 = 2^119 * z := by unfold z; ring
  rw [he, log_mul (by positivity) hz.ne', log_pow]
  have hz' : (z:ℝ)⁻¹ ≤ 0.84 := by norm_num [z,scale,δ]
  linarith [log_two_gt_d9]

theorem log_large {h : ℝ} (hh : 10^30 ≤ h) : 82.65 ≤ log (scale*h) :=
  log_base_lower.trans (log_le_log (by norm_num [scale,δ]) (mul_le_mul_of_nonneg_left hh (by norm_num [scale,δ])))

private theorem log_base_upper : log (scale*baseH) ≤ 83.90 := by
  let z : ℝ := scale * baseH / 2^121
  have hz : 0 < z := by norm_num [z,scale,δ,baseH]
  have he : scale * baseH = 2^121 * z := by unfold z; ring
  rw [he, log_mul (by positivity) hz.ne', log_pow]
  have hz' : z ≤ 1.0255 := by norm_num [z,scale,δ,baseH]
  calc
    _ ≤ (121:ℝ)*0.6931471808 + (1.0255-1) := add_le_add
      (mul_le_mul_of_nonneg_left log_two_lt_d9.le (by norm_num))
      ((log_le_sub_one_of_pos hz).trans (sub_le_sub_right hz' 1))
    _ ≤ _ := by norm_num

theorem base_le_hOne {ε : ℝ} (he : 0<ε) (hε : ε≤1) : baseH ≤ hOne ε := by
  have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he hε (by norm_num : -(166/81:ℝ)≤0)
  unfold hOne
  change baseH ≤ baseH * _
  exact le_mul_of_one_le_right (by norm_num [baseH]) this

theorem sqrt_large {h : ℝ} (hh : 10^30 ≤ h) : 10^15 ≤ √h := by
  have := sqrt_le_sqrt hh
  rwa [show sqrt ((10:ℝ)^30)=10^15 by rw [show (10:ℝ)^30=(10^15)^2 by ring, sqrt_sq (by positivity)]] at this

/-- Claim 5.2A for d = 1. The two scale factors u and t record ε and
    the excess of h over h₁(ε), respectively. -/
theorem claim52A {ε h : ℝ} (he : 0<ε) (hε : ε≤1) (hh : hOne ε ≤ h) :
    71.82 * δ^2 * log (scale*h) / √h ≤ ε*(1-1/10^7) := by
  let r := ε^(-(83/81:ℝ))
  let u := ε^(-(2/81:ℝ))
  let b := sqrt baseH
  have hr : 0<r := rpow_pos_of_pos he _
  have hu : 1≤u := one_le_rpow_of_pos_of_le_one_of_nonpos he hε (by norm_num)
  have hb : (1843000000000000:ℝ)≤b := by
    apply (le_sqrt (by norm_num) (by norm_num [baseH])).mpr
    norm_num [baseH]
  have hb0 : 0<b := by linarith
  have hb2 : b^2=baseH := sq_sqrt (by norm_num [baseH])
  have rr : hOne ε = (b*r)^2 := by
    rw [mul_pow,hb2, hOne]
    congr 1
    rw [← Real.rpow_natCast (x := r) (n := 2), show r=ε^(-(83/81:ℝ)) from rfl,
      ← Real.rpow_mul he.le]
    norm_num
  have hs : b*r ≤ √h := by
    apply (le_sqrt (mul_nonneg hb0.le hr.le) _).mpr
    · rwa [← rr]
    · rw [rr] at hh; first | positivity | nlinarith
  have hs0 : 0<√h := (mul_pos hb0 hr).trans_le hs
  let t := √h / (b*r)
  have ht : 1≤t := (one_le_div (mul_pos hb0 hr)).mpr hs
  have ht0 : 0<t := by linarith
  have hs_eq : √h=b*r*t := by unfold t; field_simp
  have hpos : 0≤h := by rw [rr] at hh; linarith [sq_nonneg (b*r)]
  have hfac : scale*h = scale*baseH * r^2 * t^2 := by
    rw [← sq_sqrt hpos, hs_eq,← hb2]; ring
  have hrlog : 2*log r = 83*log u := by
    simp only [r,u,log_rpow he]; ring
  have her : ε*r=u := by
    calc
      ε*r = ε^(1:ℝ)*ε^(-(83/81:ℝ)) := by rw [rpow_one]
      _ = u := by rw [← rpow_add he]; norm_num [u]
  have hlog : log (scale*h) ≤ 83.90*(u*t) := by
    rw [hfac,log_mul (by positivity) (pow_ne_zero _ ht0.ne'),log_mul (by norm_num [scale,δ,baseH])
      (pow_ne_zero _ hr.ne'),log_pow,log_pow]
    push_cast
    nlinarith only [log_base_upper,hrlog,log_le_sub_one_of_pos (by linarith : 0<u),
      log_le_sub_one_of_pos ht0,hu,ht,mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr ht)]
  apply (div_le_iff₀ hs0).mpr
  have ha := mul_le_mul_of_nonneg_left hlog (by norm_num [δ] : 0≤71.82*δ^2)
  have hbnd : 71.82*δ^2*83.90 ≤ (1-1/10^7)*b := by dsimp [δ]; linarith only [hb]
  calc
    _ ≤ 71.82*δ^2*(83.90*(u*t)) := ha
    _ ≤ (1-1/10^7)*b*(u*t) := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbnd (by positivity)
    _ = ε*(1-1/10^7)*√h := by rw [hs_eq,← her]; ring

/-- Two logarithmic bounds from (P1), pp. 39 and 42. -/
theorem prime_log_bounds {h l : ℝ} (hh : 10^30≤h) (hl : 0<l)
    (hupper : l≤1.464*δ*√h*log (scale*h)) :
    log l ≤ 1.5*log h+2*log (2*δ) ∧ log l ≤ 2*log (scale*h) := by
  have hpos : 0<h := by linarith only [hh,show (0:ℝ)<10^30 by norm_num]
  have hs := sqrt_large hh
  have hs0 := sqrt_pos.mpr hpos
  have hs2 := sq_sqrt hpos.le
  have ha : 0<scale*h := mul_pos (by norm_num [scale,δ]) hpos
  have hx := (mul_le_mul_of_nonneg_left (Real.log_le_self ha.le)
    (show 0≤1.464*δ*√h by positivity))
  constructor
  · have H : l≤(2*δ)^2*(√h)^3 := by
      apply hupper.trans (hx.trans _)
      rw [← hs2, sqrt_sq hs0.le]; dsimp [scale,δ]; nlinarith only [pow_nonneg hs0.le 3]
    have H' := log_le_log hl H
    rw [log_mul (by norm_num [δ]) (pow_ne_zero _ hs0.ne'),log_pow,log_pow,log_sqrt hpos.le] at H'
    linarith
  · have hsle : 1.464*δ*√h ≤ scale*h := by
      rw [← hs2,sqrt_sq hs0.le]; dsimp [scale,δ]
      nlinarith only [mul_nonneg hs0.le (show 0≤√h-2 by linarith only [hs,show (2:ℝ)≤10^15 by norm_num])]
    have H : l ≤ (scale*h)^2 := hupper.trans (hx.trans (by rw [sq]; exact mul_le_mul_of_nonneg_right hsle ha.le))
    simpa only [log_pow, Nat.cast_ofNat] using log_le_log hl H

/-- Strict positivity of the f(h) used to force a bad place away from l. -/
theorem f_positive {h : ℝ} (hh : 10^30≤h) : 0 < √h - 1.5*log h - 2*log (2*δ) := by
  have hs := sqrt_large hh
  have hs0 : 0<√h := by linarith only [hs,show (0:ℝ)<10^15 by norm_num]
  have h0 : 0≤h := by linarith only [hh,show (0:ℝ)≤10^30 by norm_num]
  have hd := log_le_log (by norm_num [δ] : (0:ℝ)<2*δ) (show 2*δ≤√h by dsimp [δ]; linarith only [hs])
  have hv := log_le_sub_one_of_pos (div_pos hs0 (by norm_num : (0:ℝ)<16))
  rw [log_div hs0.ne' (by norm_num)] at hv
  have := Real.log_le_self (by norm_num : (0:ℝ)≤16)
  have hlog := log_sqrt h0
  have hlog' : 5 * log (√h) < √h := by linarith only [hv,this,hs]
  rw [show log h = 2*log (√h) by linarith only [hlog]]
  apply sub_pos.mpr
  calc
    2*log (2*δ) ≤ 2*log (√h) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ < _ := by linarith only [hlog']

theorem claim52B {ε h l : ℝ} (he : 0<ε) (hε : ε≤1) (hh : hOne ε≤h)
    (hl : 0<l) (hupper : l≤1.464*δ*√h*log (scale*h)) :
    (2*log l + 71.82*δ^2*log (scale*h)+δ)/√h ≤ ε := by
  have h0 : 10^30≤h := (show (10:ℝ)^30≤baseH by norm_num [baseH]).trans ((base_le_hOne he hε).trans hh)
  have hs : 0<√h := by have := sqrt_large h0; linarith only [this,show (0:ℝ)<10^15 by norm_num]
  have hA := (div_le_iff₀ hs).mp (claim52A he hε hh)
  have hB := (prime_log_bounds h0 hl hupper).2
  have hL := log_large h0
  have hD : δ ≤ (1/10^8)*(71.82*δ^2*log (scale*h)) := by dsimp [δ]; linarith only [hL]
  have hl' : 2*log l ≤ (1/10^12)*(71.82*δ^2*log (scale*h)) := by
    calc
      _ ≤ 4*log (scale*h) := by linarith only [hB]
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by norm_num [δ]) ((show (0:ℝ)≤82.65 by norm_num).trans hL)
  apply (div_le_iff₀ hs).mpr
  nlinarith only [hl',hD,hA,mul_nonneg he.le hs.le]

end
end ExpEstL3
