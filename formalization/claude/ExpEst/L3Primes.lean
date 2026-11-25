import ExpEst.L3Num
import Mathlib.NumberTheory.Primorial

/-!
# L3, the choice of the prime `l` in Corollary 5.2 (pp. 37–40)

* `PlaceData` models the data of the proof of Corollary 5.2 that the numeric argument uses:
  a finite family of places `v ∈ V(F)^non` containing those with `h_v ≠ 0` (bad multiplicative
  reduction; entries with `h_v = 0` are allowed and contribute nothing), with residue
  characteristic `p_v`, residue degree `f_v ≥ 1`, local height `h_v`, and `N = [F : ℚ]`.
  The constraint `∑_{p_v = q} f_v ≤ N` holds since `∑_{v | q} e_v·f_v = [F : ℚ]` and `e_v ≥ 1`.
  The type records only these numbers, not the field, the places or the reduction.
* `height P = (1/N)·∑_v h_v·f_v·log p_v` is `h = log(𝔮^∀)` (p. 37);
  `logq P l` is the same sum over the places with `p_v ≠ l`: the `log 𝔮` of Theorem 5.1 when its
  support is chosen as in (P5) of Corollary 5.2 (all bad multiplicative places not above `l`).
* `PNT_lower` is the lower half of Proposition 2.2 (ii): `θ(x) ≥ (1 - 0.00071)·x` for
  `x ≥ ξ_prm = 10^15`.  This is an input (not proved here).  The upper half of
  Proposition 2.2 (ii) is replaced by `θ(x) ≤ log 4 · x` (Mathlib's `primorial_le_four_pow`).
-/

namespace ExpEst

open Real Finset

/-- `θ_A = ∑_{q ∈ A} log q`. -/
noncomputable def thetaSet (A : Finset ℕ) : ℝ := ∑ q ∈ A, Real.log q

/-- The primes `≤ x`. -/
noncomputable def primesUpTo (x : ℝ) : Finset ℕ := (range (⌊x⌋₊ + 1)).filter Nat.Prime

/-- Chebyshev's `θ(x) = ∑_{p ≤ x} log p`. -/
noncomputable def theta (x : ℝ) : ℝ := thetaSet (primesUpTo x)

/-- **Input (Proposition 2.2 (ii), lower half)**: `θ(x) ≥ (1 - 0.00071)·x` for `x ≥ 10^15`. -/
def PNT_lower : Prop := ∀ x : ℝ, (10 : ℝ) ^ 15 ≤ x → (1 - 0.00071) * x ≤ theta x

theorem thetaSet_nonneg (A : Finset ℕ) : 0 ≤ thetaSet A :=
  sum_nonneg fun q _ => Real.log_natCast_nonneg q

/-- Proposition 2.2 (ii), "in particular" part: for any finite `A` there is a prime `l ∉ A`
with `l ≤ 1.00072·(θ_A + ξ_prm)`.  (The sharper `(1 - 0.00071)^{-1}·(θ_A + ξ_prm)` is the cutoff
used inside the proof; the statement returns only the rounded bound.) -/
theorem exists_prime_not_mem (H : PNT_lower) (A : Finset ℕ) :
    ∃ l : ℕ, l.Prime ∧ l ∉ A ∧ (l : ℝ) ≤ 1.00072 * (thetaSet A + 10 ^ 15) := by
  have hA0 := thetaSet_nonneg A
  set x : ℝ := (thetaSet A + 10 ^ 15) / (1 - 0.00071) with hx
  have hx15 : (10 : ℝ) ^ 15 ≤ x := by rw [hx, le_div_iff₀ (by norm_num)]; nlinarith
  have hθ := H x hx15
  have hxeq : (1 - 0.00071) * x = thetaSet A + 10 ^ 15 := by rw [hx]; field_simp
  by_contra hne
  push Not at hne
  have hsub : primesUpTo x ⊆ A := by
    intro q hq
    by_contra hqA
    have hq' := mem_filter.mp hq
    have hqx : (q : ℝ) ≤ x := by
      have h1 : q ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp hq'.1)
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
    have := hne q hq'.2 hqA
    have hxle : x ≤ 1.00072 * (thetaSet A + 10 ^ 15) := by
      rw [hx, div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have : theta x ≤ thetaSet A :=
    sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => Real.log_natCast_nonneg q
  have h15 : (0 : ℝ) < 10 ^ 15 := by norm_num
  linarith

/-- `θ(x) ≤ 2x` for `x ≥ 0` (replaces `θ(x) ≤ 1.00071·x ≤ 2x`, p. 38).  The proof goes through
`θ(x) ≤ log 4 · x`; the statement returns only `2x`. -/
theorem theta_le_two_mul {x : ℝ} (hx : 0 ≤ x) : theta x ≤ 2 * x := by
  have hprod : theta x = Real.log (primorial ⌊x⌋₊) := by
    rw [theta, thetaSet, primesUpTo, primorial, Nat.cast_prod, Real.log_prod]
    intro q hq
    exact Nat.cast_ne_zero.mpr (mem_filter.mp hq).2.ne_zero
  have h4 : Real.log (primorial ⌊x⌋₊) ≤ ⌊x⌋₊ * Real.log 4 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast primorial_pos _)
    exact_mod_cast primorial_le_four_pow _
  have hl4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hprod]; nlinarith

/-- `θ` of the prime factors of `n ≠ 0` is at most `log n`. -/
theorem thetaSet_primeFactors_le {n : ℕ} (hn : n ≠ 0) : thetaSet n.primeFactors ≤ Real.log n := by
  rw [thetaSet, ← Real.log_prod]
  · rw [← Nat.cast_prod]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun q hq =>
        (Nat.prime_of_mem_primeFactors hq).ne_zero)
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  · intro q hq; exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hq).ne_zero

theorem thetaSet_union_le (s t : Finset ℕ) : thetaSet (s ∪ t) ≤ thetaSet s + thetaSet t := by
  have := sum_union_inter (s₁ := s) (s₂ := t) (f := fun q : ℕ => Real.log q)
  have h0 : 0 ≤ ∑ q ∈ s ∩ t, Real.log (q : ℝ) := sum_nonneg fun q _ => Real.log_natCast_nonneg q
  unfold thetaSet; linarith

theorem thetaSet_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (T : ι → Finset ℕ) :
    thetaSet (s.biUnion T) ≤ ∑ i ∈ s, thetaSet (T i) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSet]
  | insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    exact (thetaSet_union_le _ _).trans (by linarith)

theorem thetaSet_image_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℕ) :
    thetaSet (s.image g) ≤ ∑ i ∈ s, Real.log (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSet]
  | insert i s hi ih =>
    rw [image_insert, sum_insert hi, insert_eq]
    refine (thetaSet_union_le _ _).trans ?_
    simp only [thetaSet, sum_singleton] at ih ⊢
    linarith

/-- The data of `V(F)^non` used in the proof of Corollary 5.2 (see the module docstring). -/
structure PlaceData where
  n : ℕ
  N : ℕ
  hN : 0 < N
  p : Fin n → ℕ
  hp : ∀ v, (p v).Prime
  f : Fin n → ℕ
  hf : ∀ v, 1 ≤ f v
  hv : Fin n → ℕ
  hsum : ∀ q : ℕ, ∑ v ∈ univ.filter (fun v => p v = q), f v ≤ N

namespace PlaceData

variable (P : PlaceData)

/-- `h_v·f_v·log p_v`. -/
noncomputable def a (v : Fin P.n) : ℝ := P.hv v * P.f v * Real.log (P.p v)

/-- `h = log(𝔮^∀) = (1/[F:ℚ])·∑_v h_v·f_v·log p_v` (p. 37). -/
noncomputable def height : ℝ := (∑ v, P.a v) / P.N

/-- `log 𝔮` of Theorem 5.1 for the prime `l`, with the support chosen as in (P5) of
Corollary 5.2: the same sum over the places with `p_v ≠ l`. -/
noncomputable def logq (l : ℕ) : ℝ := (∑ v ∈ univ.filter (fun v => P.p v ≠ l), P.a v) / P.N

theorem a_nonneg (v : Fin P.n) : 0 ≤ P.a v := by
  unfold a; have := Real.log_natCast_nonneg (P.p v); positivity

theorem N_pos : (0 : ℝ) < P.N := by exact_mod_cast P.hN

theorem sum_a_eq : ∑ v, P.a v = P.N * P.height := by
  rw [height]; field_simp [P.N_pos.ne']

/-- From (P3): `h - log 𝔮 ≤ h^{1/2}·log l` (p. 40). -/
theorem height_sub_logq_le (l : ℕ) (hP3 : ∀ v, P.p v = l → (P.hv v : ℝ) < √P.height) :
    P.height - P.logq l ≤ √P.height * Real.log l := by
  have hsplit := sum_filter_add_sum_filter_not (s := (univ : Finset (Fin P.n)))
    (p := fun v => P.p v = l) (f := P.a)
  have hdiff : P.height - P.logq l = (∑ v ∈ univ.filter (fun v => P.p v = l), P.a v) / P.N := by
    rw [logq, height, ← hsplit]; ring
  rw [hdiff, div_le_iff₀ P.N_pos]
  have hl0 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
  calc ∑ v ∈ univ.filter (fun v => P.p v = l), P.a v
      ≤ ∑ v ∈ univ.filter (fun v => P.p v = l), √P.height * Real.log l * P.f v := by
        apply sum_le_sum
        intro v hv
        have hpv := (mem_filter.mp hv).2
        rw [a, hpv]
        have := hP3 v hpv
        have hf0 : (0 : ℝ) ≤ P.f v := by positivity
        nlinarith [mul_nonneg hf0 hl0]
    _ = √P.height * Real.log l * (∑ v ∈ univ.filter (fun v => P.p v = l), (P.f v : ℝ)) := by
        rw [mul_sum]
    _ ≤ √P.height * Real.log l * P.N := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast P.hsum l
    _ = √P.height * Real.log l * P.N := rfl

/-- (P5) (pp. 39–40): if `h > 0`, (P3) holds and `log l < h^{1/2}`, then some place `v` with
`h_v ≠ 0` (bad multiplicative reduction) has `p_v ≠ l`, i.e. `V^bad_mod ≠ ∅`. -/
theorem exists_bad_place (l : ℕ) (hh : 0 < P.height)
    (hP3 : ∀ v, P.p v = l → (P.hv v : ℝ) < √P.height) (hlt : Real.log l < √P.height) :
    ∃ v, P.hv v ≠ 0 ∧ P.p v ≠ l := by
  by_contra hne
  push Not at hne
  have hq0 : P.logq l = 0 := by
    rw [logq]
    have : ∑ v ∈ univ.filter (fun v => P.p v ≠ l), P.a v = 0 := by
      apply sum_eq_zero
      intro v hv
      have hpv := (mem_filter.mp hv).2
      have h0 : P.hv v = 0 := by
        by_contra h0; exact hpv (hne v h0)
      simp [a, h0]
    rw [this, zero_div]
  have h1 := P.height_sub_logq_le l hP3
  rw [hq0, sub_zero] at h1
  have hs0 : 0 < √P.height := Real.sqrt_pos.mpr hh
  have h2 : √P.height * Real.log l < √P.height * √P.height := mul_lt_mul_of_pos_left hlt hs0
  rw [Real.mul_self_sqrt hh.le] at h2
  linarith

/-- The places with `h_v ≥ h^{1/2}`. -/
noncomputable def big : Finset (Fin P.n) := univ.filter (fun v => √P.height ≤ P.hv v)

/-- The set `𝒜` of (S1)–(S3) (p. 38).  For (S2) only the `h_v ≥ h^{1/2}` are listed: a prime
dividing an `h_v < h^{1/2}` is `< h^{1/2}`, so it is already in (S1). -/
noncomputable def A : Finset ℕ :=
  primesUpTo √P.height ∪ (P.big.biUnion fun v => (P.hv v).primeFactors) ∪ P.big.image P.p

/-- (S3) part: `∑_{h_v ≥ h^{1/2}} log p_v ≤ N·h^{1/2}`. -/
theorem sum_big_log_p_le (hh : 1 ≤ P.height) :
    ∑ v ∈ P.big, Real.log (P.p v) ≤ P.N * √P.height := by
  have hs1 : 1 ≤ √P.height := by rw [Real.one_le_sqrt]; exact hh
  have hs0 : 0 < √P.height := by linarith
  have hterm : ∀ v ∈ P.big, Real.log (P.p v) ≤ P.a v / √P.height := by
    intro v hv
    have hbig := (mem_filter.mp hv).2
    rw [le_div_iff₀ hs0, a]
    have hl0 := Real.log_natCast_nonneg (P.p v)
    have hf1 : (1 : ℝ) ≤ P.f v := by exact_mod_cast P.hf v
    have : √P.height ≤ P.hv v * P.f v := by nlinarith
    nlinarith
  calc ∑ v ∈ P.big, Real.log (P.p v) ≤ ∑ v ∈ P.big, P.a v / √P.height := sum_le_sum hterm
    _ ≤ ∑ v, P.a v / √P.height :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ =>
          div_nonneg (P.a_nonneg v) hs0.le
    _ = P.N * √P.height := by
        rw [← sum_div, P.sum_a_eq]
        field_simp
        rw [Real.sq_sqrt (by linarith)]

/-- (S2) part: `∑_{h_v ≥ h^{1/2}} log h_v ≤ 1.45·N·h^{1/2}·log(1.45·N·h)` (p. 38). -/
theorem sum_big_log_hv_le (hh : 1 ≤ P.height) :
    ∑ v ∈ P.big, Real.log (P.hv v) ≤
      1.45 * P.N * √P.height * Real.log (1.45 * P.N * P.height) := by
  have hs1 : 1 ≤ √P.height := by rw [Real.one_le_sqrt]; exact hh
  have hs0 : 0 < √P.height := by linarith
  have hN1 : (1 : ℝ) ≤ P.N := by exact_mod_cast P.hN
  set M := Real.log (1.45 * P.N * P.height) with hM
  have hM0 : 0 ≤ M := Real.log_nonneg (by nlinarith)
  have hl2 := Real.log_two_gt_d9
  have hterm : ∀ v ∈ P.big, Real.log (P.hv v) ≤ 1.45 * M * P.a v / √P.height := by
    intro v hv
    have hbig := (mem_filter.mp hv).2
    have hhv1 : (1 : ℝ) ≤ P.hv v := hs1.trans hbig
    have hp2 : (2 : ℝ) ≤ P.p v := by exact_mod_cast (P.hp v).two_le
    have hlogp : Real.log 2 ≤ Real.log (P.p v) := Real.log_le_log (by norm_num) hp2
    have hf1 : (1 : ℝ) ≤ P.f v := by exact_mod_cast P.hf v
    have hav : (P.hv v : ℝ) ≤ 1.45 * P.a v := by
      rw [a]
      have : (1 : ℝ) ≤ 1.45 * (P.f v * Real.log (P.p v)) := by nlinarith
      nlinarith
    have haN : P.a v ≤ P.N * P.height := by
      rw [← P.sum_a_eq]
      exact single_le_sum (fun w _ => P.a_nonneg w) (mem_univ v)
    have hlogv : Real.log (P.hv v) ≤ M := by
      apply Real.log_le_log (by linarith)
      nlinarith
    have hlogv0 : 0 ≤ Real.log (P.hv v) := Real.log_nonneg hhv1
    rw [le_div_iff₀ hs0]
    -- `log h_v · h^{1/2} ≤ log h_v · h_v ≤ M · 1.45 · a_v`
    calc Real.log (P.hv v) * √P.height ≤ Real.log (P.hv v) * P.hv v :=
          mul_le_mul_of_nonneg_left hbig hlogv0
      _ ≤ M * (1.45 * P.a v) := mul_le_mul hlogv hav (by linarith) hM0
      _ = 1.45 * M * P.a v := by ring
  calc ∑ v ∈ P.big, Real.log (P.hv v) ≤ ∑ v ∈ P.big, 1.45 * M * P.a v / √P.height :=
        sum_le_sum hterm
    _ ≤ ∑ v, 1.45 * M * P.a v / √P.height :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ =>
          div_nonneg (mul_nonneg (by positivity) (P.a_nonneg v)) hs0.le
    _ = 1.45 * P.N * √P.height * M := by
        rw [← sum_div, ← mul_sum, P.sum_a_eq]
        field_simp
        rw [Real.sq_sqrt (by linarith)]

/-- `θ_𝒜 ≤ 2·h^{1/2} + N·h^{1/2} + 1.45·N·h^{1/2}·log(1.45·N·h)` (p. 38). -/
theorem thetaSet_A_le (hh : 1 ≤ P.height) :
    thetaSet P.A ≤ 2 * √P.height + P.N * √P.height
      + 1.45 * P.N * √P.height * Real.log (1.45 * P.N * P.height) := by
  have h1 := theta_le_two_mul (Real.sqrt_nonneg P.height)
  have h2 : thetaSet (P.big.biUnion fun v => (P.hv v).primeFactors) ≤
      ∑ v ∈ P.big, Real.log (P.hv v) := by
    refine (thetaSet_biUnion_le _ _).trans (sum_le_sum fun v hv => ?_)
    have hbig := (mem_filter.mp hv).2
    have hs1 : 1 ≤ √P.height := by rw [Real.one_le_sqrt]; exact hh
    have : P.hv v ≠ 0 := by
      intro h0; rw [h0, Nat.cast_zero] at hbig; linarith
    exact thetaSet_primeFactors_le this
  have h3 := thetaSet_image_le P.big P.p
  have u1 := thetaSet_union_le (primesUpTo √P.height ∪ P.big.biUnion fun v => (P.hv v).primeFactors)
    (P.big.image P.p)
  have u2 := thetaSet_union_le (primesUpTo √P.height) (P.big.biUnion fun v => (P.hv v).primeFactors)
  have s2 := P.sum_big_log_hv_le hh
  have s3 := P.sum_big_log_p_le hh
  unfold A
  unfold theta at h1
  linarith

end PlaceData

end ExpEst
