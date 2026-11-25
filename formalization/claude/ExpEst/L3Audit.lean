import ExpEst.L3Main

/-!
# L3 audit

* `#print axioms` of the main L3 theorems.
* Non-vacuity: the per-curve inputs `Cor52Input` hold for the actual curve `E_{1,1,-2}`
  (`j = 1728`, `h^non = 0`), and the hypotheses of `cor52_C2` other than `PNT_lower`
  are jointly satisfiable with `h ≥ h₁(1)`, `j ∉ excJ` (an abstract instance, not a curve).
  `PNT_lower` is not proved here (it is the lower half of Proposition 2.2 (ii), cited by the
  paper from [RS], Theorem 7).  The consistency of the universal hypothesis `Sec5Inputs` is
  not established: together with `PNT_lower` it implies the explicit Theorem 5.3 (i).
-/

namespace ExpEst

open Real

theorem PlaceData.logq_le_height (P : PlaceData) (l : ℕ) : P.logq l ≤ P.height := by
  unfold PlaceData.logq PlaceData.height
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast P.hN.le)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun v _ _ => P.a_nonneg v

/-- No places, `N = 1`: `h = 0`. -/
def emptyPlaces : PlaceData where
  n := 0
  N := 1
  hN := one_pos
  p := Fin.elim0
  hp := fun v => Fin.elim0 v
  f := Fin.elim0
  hf := fun v => Fin.elim0 v
  hv := Fin.elim0
  hsum := fun _ => by simp

theorem emptyPlaces_height : emptyPlaces.height = 0 := by
  simp [PlaceData.height, emptyPlaces]

/-- `Cor52Input` holds for the curve `E_{1,1,-2}` (`j = 1728 ∈ excJ`, `h^non(j) = 0`). -/
example : Cor52Input
    (hnon (@WeierstrassCurve.j ℚ _ (Eabc 1 1 (-2)) (Eabc_isElliptic one_ne_zero one_ne_zero
      (by norm_num) (by norm_num))))
    (Real.log (radQ 1 1 (-2)))
    (@WeierstrassCurve.j ℚ _ (Eabc 1 1 (-2)) (Eabc_isElliptic one_ne_zero one_ne_zero
      (by norm_num) (by norm_num))) := by
  have hj := example_j
  refine ⟨emptyPlaces, fun _ => False, ?_, ?_, fun _ _ _ _ hc => hc.elim, fun hnot => ?_⟩
  · rw [emptyPlaces_height, hj, example_hnon]
  · norm_num [emptyPlaces, δ₁]
  · exact (hnot (by rw [hj]; simp [excJ])).elim

/-- One place over `2` with `h_v = 5·10^30`, `N = 1`. -/
noncomputable def bigPlace : PlaceData where
  n := 1
  N := 1
  hN := one_pos
  p := fun _ => 2
  hp := fun _ => Nat.prime_two
  f := fun _ => 1
  hf := fun _ => le_rfl
  hv := fun _ => 5 * 10 ^ 30
  hsum := fun q => by
    calc ∑ v ∈ Finset.univ.filter (fun _ : Fin 1 => 2 = q), 1
        ≤ ∑ v : Fin 1, 1 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = 1 := by simp

theorem bigPlace_height : bigPlace.height = 5 * 10 ^ 30 * Real.log 2 := by
  simp [PlaceData.height, PlaceData.a, bigPlace]; norm_num

/-- The hypotheses of `cor52_C2` other than `PNT_lower` are jointly satisfiable on the branch
`h ≥ h₁(1)`, `j ∉ excJ` (abstract instance: the numbers are not those of a curve). -/
example : ∃ (h R : ℝ) (j : ℚ), h1 1 ≤ h ∧ j ∉ excJ ∧ Cor52Input h R j := by
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  refine ⟨bigPlace.height, 10 ^ 31, 2, ?_, ?_, ?_⟩
  · rw [h1_one, bigPlace_height]; nlinarith
  · simp only [excJ, Set.mem_insert_iff, Set.mem_singleton_iff]; norm_num
  · refine ⟨bigPlace, fun _ => False, rfl, ?_, fun _ _ _ _ hc => hc.elim,
      fun _ l _ _ _ _ _ _ _ _ => ⟨10 ^ 31, 0, 0, by norm_num, le_rfl, le_rfl, by norm_num [δ₁],
        by norm_num [δ₁], ?_⟩⟩
    · norm_num [bigPlace, δ₁]
    · have := bigPlace.logq_le_height l
      rw [bigPlace_height] at this
      simp only [mul_zero, zero_div, add_zero, zero_mul]
      nlinarith

#print axioms ExpEst.claim52A
#print axioms ExpEst.claim52B
#print axioms ExpEst.c2_of_p8
#print axioms ExpEst.exists_prime_not_mem
#print axioms ExpEst.exists_good_prime
#print axioms ExpEst.cor52_C2
#print axioms ExpEst.thm53i_of_inputs
#print axioms ExpEst.cor58_of_inputs

end ExpEst
