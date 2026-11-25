import Reduction
import Exceptions
import ExpEst

namespace ExpEstL3
open Real ExpEstL2
noncomputable section

/-- Abstract arithmetic data at one rational Legendre parameter. The degree,
    support and weights keep full and restricted q-degrees distinct. -/
structure ArithmeticData where
  localData : LocalData
  tripodalCost : ℕ → ℝ
  core : Prop
  cyclic : ℕ → Prop
  containsSL : ℕ → Prop
  initialData : ℕ → Prop

/-- Inputs of the numerical argument. The last field is Theorem 5.1 at
    its Θ-bound, before the rounding from 4.08803 to 4.0881. -/
structure External (D : QTriple) (M : ArithmeticData) : Prop where
  height_identity : M.localData.height = hNon D.curve.j
  core_criterion : ¬M.core → exceptionalJ D.curve.j
  cyclic_height : ∀ l : ℕ, l.Prime → (10^15:ℝ)≤l →
    (∀ v∈M.localData.places, ¬l∣M.localData.n v) → M.cyclic l →
    M.localData.height ≤ 5.12/10^13
  galois_image : ∀ l : ℕ, l.Prime → (10^15:ℝ)≤l →
    (∀ v∈M.localData.places, ¬l∣M.localData.n v) →
    ¬M.cyclic l → M.localData.Away l → M.containsSL l
  existence_initial : ∀ l : ℕ, M.core → (10^15:ℝ)≤l → M.localData.Eligible l →
    M.localData.Away l → M.containsSL l → M.initialData l
  divisor_comparison : ∀ l : ℕ, M.initialData l → 0≤M.tripodalCost l ∧
    M.tripodalCost l ≤ log D.radical
  theta51 : ∀ l : ℕ, M.initialData l → (10^15:ℝ)≤l →
    -1 ≤ thetaConstant (M.localData.restricted l) (M.tripodalCost l) l

/-- Corollary 5.2 over ℚ outside the explicitly finite exceptional set.
    The same l witnesses (C1), (P2)–(P7), and the large-height branch (C2). -/
theorem corollary52 (pnt : PrimeEstimate) {D : QTriple} {M : ArithmeticData}
    (I : External D M) {ε : ℝ} (he : 0<ε) (hε : ε≤1)
    (hout : parameter D ∉ exceptional (hOne ε)) :
    ∃ l : ℕ, M.localData.Eligible l ∧ ¬M.cyclic l ∧ M.localData.Away l ∧
      M.containsSL l ∧ M.initialData l ∧ M.localData.height/6 ≤ (1+ε)*log D.radical := by
  let T := M.localData
  have H : hOne ε < T.height := by
    rw [show T.height=hNon D.curve.j from I.height_identity]
    exact lt_of_not_ge (fun hs => hout ((mem_exceptional D).mpr hs))
  have H0 : 10^30 ≤ T.height := (show (10:ℝ)^30≤baseH by norm_num).trans
    ((base_le_hOne he hε).trans H.le)
  obtain ⟨l,E⟩ := T.select_prime pnt H0
  have hl : (10^15:ℝ)≤l := (sqrt_large H0).trans E.2.1
  have core : M.core := by
    by_contra hn
    have h1 := exceptionalJ_bound (I.core_criterion hn)
    have small := Real.log_le_self (by norm_num : (0:ℝ)≤125)
    rw [← I.height_identity] at h1
    change 10^30 ≤ M.localData.height at H0
    linarith only [h1,small,H0]
  have nc : ¬M.cyclic l := by
    intro hc
    have := I.cyclic_height l E.1 hl E.2.2.2.1 hc
    change 10^30 ≤ M.localData.height at H0
    linarith only [this,H0]
  have away := T.away_of_large H0 E
  have sl := I.galois_image l E.1 hl E.2.2.2.1 nc away
  have init := I.existence_initial l core hl E away sl
  obtain ⟨B0,BD⟩ := I.divisor_comparison l init
  have bracket := (theta51_iff (T.restricted_pos away) (show (0:ℝ)<l by exact_mod_cast E.1.pos)).mp (I.theta51 l init hl)
  have bound := estimate51 hl B0 bracket
  have mid := T.p8 H0 E B0 bound
  have c2 := T.c2_of_p8 he hε H.le E mid
  exact ⟨l,E,nc,away,sl,init,c2.trans (mul_le_mul_of_nonneg_left BD (by linarith))⟩

/-- The finite-set formulation of the numerical Corollary 5.2, including
    the four exceptional j-values and both conditions on the complement. -/
theorem finite_corollary52 (pnt : PrimeEstimate) {ε : ℝ} (he : 0<ε) (hε : ε≤1) :
    ∃ X : Set ℚ, X.Finite ∧
      (∀ D : QTriple, exceptionalJ D.curve.j → parameter D∈X) ∧
      (∀ D : QTriple, parameter D∈X → hNon D.curve.j≤hOne ε) ∧
      ∀ (D : QTriple) (M : ArithmeticData), External D M → parameter D∉X →
        ∃ l : ℕ, 10^15≤√M.localData.height ∧ M.localData.Eligible l ∧ M.initialData l ∧
          M.localData.height/6≤(1+ε)*log D.radical := by
  refine ⟨exceptional (hOne ε),exceptional_finite _,?_,fun D => (mem_exceptional D).mp,?_⟩
  · intro D hj
    apply (mem_exceptional D).mpr
    exact (exceptionalJ_bound hj).trans ((Real.log_le_self (by norm_num)).trans
      ((by norm_num [baseH] : (125:ℝ)≤baseH).trans (base_le_hOne he hε)))
  · intro D M I hout
    obtain ⟨l,E,_,_,_,initial,upper⟩ := corollary52 pnt I he hε hout
    have H := lt_of_not_ge (fun hs => hout ((mem_exceptional D).mpr hs))
    rw [← I.height_identity] at H
    exact ⟨l,sqrt_large ((show (10:ℝ)^30≤baseH by norm_num).trans
      ((base_le_hOne he hε).trans H.le)),E,initial,upper⟩

/-- The full two-part statement of the independent L2 implementation. -/
theorem theorem53i (pnt : PrimeEstimate) {D : QTriple} {M : ArithmeticData}
    (I : External D M) {ε : ℝ} (he : 0<ε) (hε : ε≤1) : Theorem53i D ε := by
  have hr : (1:ℝ)≤D.radical := by exact_mod_cast rad_pos D.primitive.product
  have u0 := mul_nonneg (show 0≤1+ε by linarith) (log_nonneg hr)
  have v0 : 0≤hOne ε/6 := by unfold hOne; positivity
  constructor
  · by_cases hx : parameter D ∈ exceptional (hOne ε)
    · exact ((div_le_div_of_nonneg_right ((mem_exceptional D).mp hx) (by norm_num : (0:ℝ)≤6))).trans
        (le_max_right ..)
    · obtain ⟨_,_,_,_,_,_,hc⟩ := corollary52 pnt I he hε hx
      rw [I.height_identity] at hc
      exact hc.trans (le_max_left ..)
  · exact max_le (le_add_of_nonneg_right v0) (le_add_of_nonneg_left u0)

/-- At ε=1 the L2 statement converts to both inequalities of L1's
    Theorem53iiQ, including the normalization by numerator and denominator. -/
theorem to_L1 (H : ∀ D : QTriple, Theorem53ii D 1) : ExpEst.Theorem53iiQ := by
  intro a b c ha hb hc habc
  let D : QTriple := ⟨a,b,c,ha,hb,hc,habc⟩
  have K := H D
  let q := a/b
  change ExpEst.estimateAt q.num.natAbs q.den (q.num+(q.den:ℤ)).natAbs
  have hHt : D.height = max q.num.natAbs (max q.den (q.num+(q.den:ℤ)).natAbs) := by
    change max q.num.natAbs (max (q.den:ℤ).natAbs (-(q.num+(q.den:ℤ))).natAbs) = _
    simp only [Int.natAbs_natCast,Int.natAbs_neg]
  have hRd : D.radical = ExpEst.primeRad (q.num.natAbs*q.den*(q.num+(q.den:ℤ)).natAbs) := by
    change ExpEst.primeRad (q.num*(q.den:ℤ)* -(q.num+(q.den:ℤ))).natAbs = _
    simp only [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_neg]
  unfold Theorem53ii at K
  rw [hHt,hRd] at K
  norm_num [hOne,ExpEst.estimateAt,ExpEst.hOne,ExpEst.heightFactor, Real.rpow_natCast] at K ⊢
  exact K

/-- The universally supplied arithmetic inputs suffice for arbitrary positive
    Fermat triples through the existing L2 (i)⇒(ii) and L1 Corollary 5.8. -/
theorem corollary58 (pnt : PrimeEstimate)
    (arithmetic : ∀ D : QTriple, ∃ M, External D M)
    {p : ℕ} (hp : p.Prime) (large : 161500000000000<p) :
    ∀ x y z : ℕ, 0<x → 0<y → 0<z → x^p+y^p ≠ z^p := by
  apply ExpEst.corollary58 _ hp large
  apply to_L1
  intro D
  obtain ⟨M,I⟩ := arithmetic D
  exact theorem53i_to_ii D (by norm_num) (by norm_num) (theorem53i pnt I (by norm_num) (by norm_num))

#print axioms coefficients51
#print axioms theta51_iff
#print axioms estimate51
#print axioms LocalData.select_prime
#print axioms f_positive
#print axioms LocalData.away_of_large
#print axioms LocalData.p8
#print axioms claim52A
#print axioms claim52B
#print axioms exceptional_finite
#print axioms corollary52
#print axioms finite_corollary52
#print axioms theorem53i
#print axioms to_L1
#print axioms corollary58

end
end ExpEstL3
