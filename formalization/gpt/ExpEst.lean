import Estimate
import Bounds

namespace ExpEst
open Real

private lemma log_contradiction {p : ℕ} {z : ℝ} (hP : 161500000000000 < p)
    (hz : 0<z) (hlarge : ((p:ℝ)+1)^p<2*z)
    (hsmall : z^p≤heightFactor*exp (hOne/4)*z^9) : False := by
  have Pgt : (161500000000000:ℝ)<p := by exact_mod_cast hP
  have h2 : (1:ℝ)<2 := by norm_num
  have hL := Real.logb_lt_logb h2 (by positivity) hlarge
  rw [Real.logb_pow, Real.logb_mul (by norm_num) hz.ne', Real.logb_self_eq_one h2] at hL
  have hU := Real.logb_le_logb_of_le h2 (pow_pos hz _) hsmall
  have hK : 0<heightFactor := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.logb_pow,Real.logb_mul (mul_pos hK (exp_pos _)).ne' (pow_ne_zero _ hz.ne'),
      Real.logb_mul hK.ne' (exp_pos _).ne', Real.logb_pow] at hU
  have lk : logb 2 heightFactor=5/2 := by
    rw [heightFactor,Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<2),Real.logb_self_eq_one h2,mul_one]
  have le : logb 2 (exp (hOne/4)) = logb 2 (exp 1)*hOne/4 := by
    simp only [Real.logb, log_exp]; ring
  rw [lk,le] at hU
  have hs : fermatLeft p < fermatRight := by
    have H := mul_lt_mul_of_pos_left (show -1+(p:ℝ)*logb 2 (p+1)<logb 2 z by linarith)
      (by linarith : 0<(p:ℝ)-9)
    unfold fermatLeft fermatRight
    linarith
  obtain ⟨h₁,h₂⟩ := paper_lower_numeric Pgt.le
  exact (lt_asymm (h₁.trans h₂) (hs.trans paper_upper_numeric))

private lemma primitive_fermat {x y z p : ℕ} (h : Theorem53iiQ) (hp : p.Prime)
    (hP : 161500000000000 < p) (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (hc : x.Coprime y) (he : x^p+y^p=z^p) : False := by
  have hi : (x:ℤ)^p+(y:ℤ)^p=(z:ℤ)^p := by exact_mod_cast he
  have hlo := lemma57 hp (by omega) (by exact_mod_cast hx) (by exact_mod_cast hy)
    (by exact_mod_cast hz) hc.isCoprime hi
  have hl : ((p:ℝ)+1)^p < 2*(z:ℝ) := by exact_mod_cast hlo
  have H := primitive_bound h (pow_pos hx p) (pow_pos hy p) ((hc.pow_left p).pow_right p)
  rw [he,← mul_pow,← mul_pow] at H
  simp only [primeRad,Nat.primeFactors_pow _ hp.ne_zero] at H
  have hrad : primeRad (x*y*z) ≤ x*y*z :=
    Nat.le_of_dvd (by positivity) (Nat.prod_primeFactors_dvd _)
  have hxz : x≤z := le_of_pow_le_pow_left₀ hp.ne_zero (Nat.zero_le _) (by omega : x^p≤z^p)
  have hyz : y≤z := le_of_pow_le_pow_left₀ hp.ne_zero (Nat.zero_le _) (by omega : y^p≤z^p)
  have hm : x*y*z ≤ z^3 := by
    calc
      x*y*z ≤ z*z*z := Nat.mul_le_mul_right _ (Nat.mul_le_mul hxz hyz)
      _ = _ := by ring
  have hr : (primeRad (x*y*z):ℝ) ≤ (z:ℝ)^3 := by exact_mod_cast hrad.trans hm
  have hK : 0<heightFactor := Real.rpow_pos_of_pos (by norm_num) _
  apply log_contradiction hP (by exact_mod_cast hz) hl
  calc
    (z:ℝ)^p ≤ heightFactor*exp (hOne/4)*(primeRad (x*y*z):ℝ)^3 := by exact_mod_cast H
    _ ≤ heightFactor*exp (hOne/4)*((z:ℝ)^3)^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr 3) (mul_pos hK (exp_pos _)).le
    _ = _ := by ring

/-- Corollary 5.8 for arbitrary positive integers, with 5.3(ii) as a parameter. -/
theorem corollary58 (h : Theorem53iiQ) {p : ℕ} (hp : p.Prime)
    (hP : 161500000000000 < p) :
    ∀ x y z : ℕ, 0<x → 0<y → 0<z → x^p+y^p ≠ z^p := by
  suffices flt : FermatLastTheoremFor p from fun x y z hx hy hz =>
    flt x y z hx.ne' hy.ne' hz.ne'
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro x y z hx hy hz hg he
  have hc : x.Coprime y := by
    apply Nat.coprime_of_dvd
    intro l hl dlx dly
    have dlz : l∣z := hl.dvd_of_dvd_pow (he ▸ dvd_add (dvd_pow dlx hp.ne_zero) (dvd_pow dly hp.ne_zero))
    apply hl.not_dvd_one
    rw [← hg]
    apply Finset.dvd_gcd_iff.mpr
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl <;> assumption
  exact primitive_fermat h hp hP (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz) hc he

#print axioms lemma57
#print axioms corollary58

end ExpEst
