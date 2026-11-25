import HeightComparison

namespace ExpEstL2
open Real

noncomputable def hOne (ε : ℝ) : ℝ := 3.4*10^30 * ε^(-(166/81:ℝ))

/-- Both inequalities of 5.3(i), evaluated at one rational triple and one ε. -/
def Theorem53i (D : QTriple) (ε : ℝ) : Prop :=
  let U := (1+ε)*log D.radical
  let V := hOne ε/6
  hNon D.curve.j/6 ≤ max U V ∧ max U V ≤ U+V

def Theorem53ii (D : QTriple) (ε : ℝ) : Prop :=
  let K := (2:ℝ)^(5/2:ℝ)
  let E := exp (hOne ε/4)
  let R := (D.radical:ℝ)^(3*(1+ε)/2)
  (D.height:ℝ) ≤ K*max E R ∧ K*max E R ≤ K*E*R

def Theorem54 (T : Primitive) (ε : ℝ) : Prop :=
  let E := exp (1.7*10^30*ε^(-(166/81:ℝ)))
  let R := (rad T.product:ℝ)^(3*(1+ε))
  (T.product:ℝ) ≤ (2:ℝ)^4*max E R ∧ (2:ℝ)^4*max E R ≤ (2:ℝ)^4*E*R

private lemma max_bound_product {K E R : ℝ} (hK : 0≤K) (hE : 1≤E) (hR : 1≤R) :
    K*max E R ≤ K*E*R := by
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hK
  exact max_le (le_mul_of_one_le_right (by linarith) hR) (le_mul_of_one_le_left (by linarith) hE)

private lemma hOne_pos {ε : ℝ} (he : 0<ε) : 0<hOne ε := by
  unfold hOne
  positivity

/-- Exponentiate a maximum at positive height and radical. -/
private lemma exp_log_estimate {X R t u v : ℝ} (hX : 0<X) (hR : 0<R)
    (h : log X ≤ log 2*t + max u (log R*v)) :
    X ≤ (2:ℝ)^t * max (exp u) (R^v) := by
  have hh := exp_le_exp.mpr h
  rwa [exp_log hX,exp_add,← rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    exp_monotone.map_max,← rpow_def_of_pos hR] at hh

/-- Theorem 5.3(i) implies 5.3(ii) for the very same rational triple and ε. -/
theorem theorem53i_to_ii (D : QTriple) {ε : ℝ} (he : 0<ε) (_hε : ε≤1)
    (h : Theorem53i D ε) : Theorem53ii D ε := by
  have hr : (1:ℝ)≤D.radical := by exact_mod_cast rad_pos D.primitive.product
  have hUpper := h.1
  change hNon D.curve.j/6 ≤ max ((1+ε)*log D.radical) (hOne ε/6) at hUpper
  have hc := claim53C D
  have hh : log D.height ≤ log 2*(5/2) + max (hOne ε/4) (log D.radical*(3*(1+ε)/2)) := by
    rcases le_total ((1+ε)*log D.radical) (hOne ε/6) with hl|hl
    · rw [max_eq_right hl] at hUpper
      linarith [le_max_left (hOne ε/4) (log D.radical*(3*(1+ε)/2))]
    · rw [max_eq_left hl] at hUpper
      linarith [le_max_right (hOne ε/4) (log D.radical*(3*(1+ε)/2))]
  refine ⟨exp_log_estimate (by exact_mod_cast D.primitive.height_pos) (by linarith) hh,?_⟩
  apply max_bound_product (by positivity) (one_le_exp (by linarith [hOne_pos he]))
  exact one_le_rpow hr (by linarith)

/-- Theorem 5.4 for nonzero primitive integer triples. The premise is only
    5.3(i) on this integer triple viewed over ℚ, at this ε. -/
theorem theorem54 (T : Primitive) {ε : ℝ} (he : 0<ε) (_hε : ε≤1)
    (h : Theorem53i T.asQ ε) : Theorem54 T ε := by
  let R : ℝ := rad T.product
  let V := 1.7*10^30*ε^(-(166/81:ℝ))
  have hr : 1≤R := by dsimp [R]; exact_mod_cast (show 1≤rad T.product from rad_pos T.product)
  have hv : hOne ε/2=V := by unfold hOne V; ring
  have hUpper := h.1
  change hNon T.asQ.curve.j/6 ≤ max ((1+ε)*log T.asQ.radical) (hOne ε/6) at hUpper
  rw [T.radical_asQ] at hUpper
  change hNon T.asQ.curve.j/6 ≤ max ((1+ε)*log R) (hOne ε/6) at hUpper
  have ht := toric_comparison T
  rw [T.torSum_eq] at ht
  have hProd : log T.product ≤ log 2*4 + max V (log R*(3*(1+ε))) := by
    rcases le_total ((1+ε)*log R) (hOne ε/6) with hl|hl
    · rw [max_eq_right hl] at hUpper
      linarith [le_max_left V (log R*(3*(1+ε)))]
    · rw [max_eq_left hl] at hUpper
      linarith [le_max_right V (log R*(3*(1+ε)))]
  have hh := exp_log_estimate (by exact_mod_cast T.product_pos) (by linarith : 0<R) hProd
  rw [show (4:ℝ)=((4:ℕ):ℝ) by norm_num, rpow_natCast] at hh
  refine ⟨hh,?_⟩
  apply max_bound_product (by norm_num) (one_le_exp (by change 0≤V; linarith [hOne_pos he]))
  exact one_le_rpow hr (by linarith)

#print axioms theorem53i_to_ii
#print axioms theorem54

end ExpEstL2
