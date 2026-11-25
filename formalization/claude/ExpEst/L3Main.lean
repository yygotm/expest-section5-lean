import ExpEst.L3Primes
import ExpEst.L2Link

/-!
# L3: the inputs of Corollary 5.2 imply Theorem 5.3 (i) over `ℚ`

`Cor52Input h R j` collects, for one curve `E_{a,b,c}` (with `h = h^non(j)`,
`R = log rad_ℚ(a, b, c)`, `j = j(E_{a,b,c})`; the three arguments are independent in the
definition and are tied to one curve only in `Sec5Inputs`), the inputs that the numeric argument
of Corollary 5.2 receives (Theorem 5.1, Corollary 1.14 (iii), Proposition 2.1, Remark 1.10.1, the
degree bounds).  `thm53i_of_inputs` derives `Thm53i_Q ε` (L2's statement, the first form
`h/6 ≤ max(…)` of Theorem 5.3 (i)) for every `0 < ε ≤ 1` from `PNT_lower` and these inputs;
`cor58_of_inputs` closes the chain to Corollary 5.8.
-/

namespace ExpEst

open Real

/-- The four `j`-invariants of Proposition 2.1: if the once-punctured curve has no `F`-core,
then `j` is one of `2^14·31^3·5^{-3}`, `2^2·73^3·3^{-4}`, `1728`, `0`.  (Only this direction is
used: `j ∉ excJ` gives an `F`-core.) -/
def excJ : Set ℚ := {488095744 / 125, 1556068 / 81, 1728, 0}

/-- **Inputs for one curve.**  There are
* place data `P` (the `v ∈ V(F)^non` with bad multiplicative reduction, over the field `F` of
  Corollary 5.2) with `h = log(𝔮^∀) = h^non(j)` [Remark 1.10.1] and `[F : ℚ] ≤ δ`
  [[IUTchIV], proof of Thm 1.10, (E3)–(E5)];
* a predicate `cyc l` ("`E_F` admits an `l`-cyclic subgroup scheme", [GenEll] Lemma 3.5; the type
  does not tie `cyc` to subgroup schemes: only the consequence below is used),
such that
* **Corollary 1.14 (iii)** with Remark 1.10.1: for a prime `l ≥ 10^15` prime to every nonzero
  `h_v`, an `l`-cyclic subgroup scheme forces `h ≤ 5.12·10^{-13}` (p. 39);
* **Theorem 5.1**, only for the primes `l` that the proof selects: if `j ∉ excJ` (so the curve has
  an `F`-core by Proposition 2.1), `l` is prime with (P1) `10^15 ≤ h^{1/2} ≤ l ≤
  1.464·δ·h^{1/2}·log(1.45·δ·h)`, (P2), (P3), (P4) no `l`-cyclic subgroup scheme, and a bad
  multiplicative place not above `l` (P5), then there are reals `D = log 𝔡^{F_tpd} + log 𝔣^{F_tpd}`
  (which may depend on `l`), `d_mod`, `e*_mod` with
  - `0 ≤ D ≤ R`: `D ≤ log-diff_X(x_E) + log-cond_D(x_E)` (p. 43) and, over `ℚ`,
    `log-diff + log-cond ≤ log(Δ_ℚ·rad_ℚ(a,b,c))` ("the various definitions", p. 43);
  - `0 ≤ d_mod`, `20·d_mod ≤ δ`, `e*_mod ≤ δ`: consequences of `20·d_mod ≤ d*_mod ≤ δ` and
    `e*_mod ≤ d*_mod` (p. 40; `d*_mod` itself is not recorded);
  - `(1/6)·log 𝔮 ≤ (1 + 20·d_mod/l)·D + 4.0881·e*_mod·l` (p. 34, p. 40).
  The Galois image (P6) and the initial Θ-data (P7), through which the paper reaches Theorem 5.1,
  are not separate inputs: only the resulting inequality is assumed. -/
def Cor52Input (h R : ℝ) (j : ℚ) : Prop :=
  ∃ (P : PlaceData) (cyc : ℕ → Prop),
    P.height = h ∧ (P.N : ℝ) ≤ δ₁ ∧
    (∀ l : ℕ, l.Prime → (10 : ℝ) ^ 15 ≤ l → (∀ v, P.hv v ≠ 0 → ¬ l ∣ P.hv v) → cyc l →
      h ≤ 5.12 * 10 ^ (-13 : ℤ)) ∧
    (j ∉ excJ → ∀ l : ℕ, l.Prime → (10 : ℝ) ^ 15 ≤ √h →
      √h ≤ l → (l : ℝ) ≤ 1.464 * δ₁ * √h * Real.log (1.45 * δ₁ * h) →
      (∀ v, P.hv v ≠ 0 → ¬ l ∣ P.hv v) → (∀ v, P.p v = l → (P.hv v : ℝ) < √h) →
      ¬ cyc l → (∃ v, P.hv v ≠ 0 ∧ P.p v ≠ l) →
      ∃ D dmod emod : ℝ, 0 ≤ D ∧ D ≤ R ∧ 0 ≤ dmod ∧ 20 * dmod ≤ δ₁ ∧ emod ≤ δ₁ ∧
        P.logq l / 6 ≤ (1 + 20 * dmod / l) * D + 4.0881 * emod * l)

/-- `L = log(1.45·δ·h) ≥ 82` when `h ≥ 10^30`. -/
theorem L_ge_82 {h : ℝ} (hh : (10 : ℝ) ^ 30 ≤ h) : 82 ≤ Real.log (1.45 * δ₁ * h) := by
  have := two_pow_le_log (1.45 * δ₁ * h) 119 (by norm_num [δ₁] at hh ⊢; nlinarith)
  have l2 := Real.log_two_gt_d9
  push_cast at this; linarith

/-- **Choice of `l`** (pp. 38–39): with `h ≥ 10^30` and `[F:ℚ] ≤ δ`, Proposition 2.2 (ii) gives a
prime `l` with (P1) `h^{1/2} ≤ l ≤ 1.464·δ·h^{1/2}·log(1.45·δ·h)`, (P2) `l ∤ h_v` for `h_v ≠ 0`,
(P3) `p_v = l ⇒ h_v < h^{1/2}`.  (The paper's lower bound `10^15·d ≤ h^{1/2}` is `sqrt_ge_of_ge`.) -/
theorem exists_good_prime (PNT : PNT_lower) (P : PlaceData) (hh : (10 : ℝ) ^ 30 ≤ P.height)
    (hN : (P.N : ℝ) ≤ δ₁) :
    ∃ l : ℕ, l.Prime ∧ √P.height ≤ l ∧
      (l : ℝ) ≤ 1.464 * δ₁ * √P.height * Real.log (1.45 * δ₁ * P.height) ∧
      (∀ v, P.hv v ≠ 0 → ¬ l ∣ P.hv v) ∧ (∀ v, P.p v = l → (P.hv v : ℝ) < √P.height) := by
  obtain ⟨l, hlp, hlA, hlb⟩ := exists_prime_not_mem PNT P.A
  have hs15 := sqrt_ge_of_ge hh
  set s := √P.height with hs
  have hh1 : 1 ≤ P.height := by linarith
  -- (S1): `l > h^{1/2}`
  have hl1 : s < l := by
    have hnot : l ∉ primesUpTo s := fun hm => hlA (Finset.mem_union_left _
      (Finset.mem_union_left _ hm))
    have hge : ⌊s⌋₊ + 1 ≤ l := by
      by_contra hlt
      push Not at hlt
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hlp⟩)
    have := Nat.lt_floor_add_one s
    have : ((⌊s⌋₊ + 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast hge
    push_cast at this
    linarith
  refine ⟨l, hlp, hl1.le, ?_, ?_, ?_⟩
  · -- the upper bound in (P1)
    have hθ := P.thetaSet_A_le hh1
    have hN1 : (1 : ℝ) ≤ P.N := by exact_mod_cast P.hN
    set L := Real.log (1.45 * δ₁ * P.height) with hL
    have hL82 := L_ge_82 hh
    have hM : Real.log (1.45 * P.N * P.height) ≤ L := by
      apply Real.log_le_log (by positivity)
      have : (0 : ℝ) ≤ P.height := by linarith
      nlinarith
    have hM0 : 0 ≤ Real.log (1.45 * P.N * P.height) := Real.log_nonneg (by nlinarith)
    have hs0 : 0 ≤ s := by linarith
    have hθ' : thetaSet P.A ≤ 2 * s + δ₁ * s + 1.45 * δ₁ * s * L := by
      have e1 : (P.N : ℝ) * s ≤ δ₁ * s := mul_le_mul_of_nonneg_right hN hs0
      have e2 : 1.45 * P.N * s * Real.log (1.45 * P.N * P.height) ≤ 1.45 * δ₁ * s * L := by
        have := mul_le_mul hN hM hM0 (by norm_num [δ₁])
        nlinarith
      linarith
    have hδ : δ₁ = 552960 := rfl
    rw [hδ] at hθ' ⊢
    nlinarith
  · -- (P2)
    intro v hv0 hdvd
    by_cases hb : s ≤ P.hv v
    · apply hlA
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩,
        Nat.mem_primeFactors.mpr ⟨hlp, hdvd, hv0⟩⟩
    · push Not at hb
      have : (l : ℝ) ≤ P.hv v := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) hdvd
      linarith
  · -- (P3)
    intro v hpv
    by_contra hb
    push Not at hb
    exact hlA (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, hpv⟩))

/-- **Corollary 5.2 (C2), numeric skeleton** (`d = 1`): from `PNT_lower` and the inputs, if
`j ∉ excJ`, `0 < ε ≤ 1` and `h ≥ h₁(ε)`, then `(1/6)·h ≤ (1 + ε)·R`. -/
theorem cor52_C2 (PNT : PNT_lower) {ε h R : ℝ} {j : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hj : j ∉ excJ) (hh : h1 ε ≤ h) (IN : Cor52Input h R j) : h / 6 ≤ (1 + ε) * R := by
  obtain ⟨P, cyc, hPh, hN, hcyc, h51⟩ := IN
  have h34 := le_of_h1_le hε hε1 hh
  have hh30 : (10 : ℝ) ^ 30 ≤ h := by linarith
  subst hPh
  obtain ⟨l, hlp, hl1, hl2, hP2, hP3⟩ := exists_good_prime PNT P hh30 hN
  have hl15 : (10 : ℝ) ^ 15 ≤ l := (sqrt_ge_of_ge hh30).trans hl1
  have hh0 : 0 < P.height := by linarith
  have hl0 : (0 : ℝ) < l := by linarith
  -- (P4)
  have hP4 : ¬ cyc l := fun hc => by
    have := hcyc l hlp hl15 hP2 hc
    norm_num at this; linarith
  -- (P5)
  have hlog := log_l_lt_sqrt hh30 hl0 hl2
  have hP5 := P.exists_bad_place l hh0 hP3 hlog
  -- Theorem 5.1, then (P8) and Claim 5.2B
  obtain ⟨D, dmod, emod, hD0, hDR, hd0, hd, he, hT51⟩ := h51 hj l hlp (sqrt_ge_of_ge hh30) hl1 hl2 hP2 hP3 hP4 hP5
  have hT := thm51_eval hh0 hl1 hl2 hD0 hd0 hd he hT51 (P.height_sub_logq_le l hP3)
  have hB := claim52B hε hε1 hh hl1 hl2
  have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hlp.one_lt.le
  have hL0 : 0 ≤ Real.log (1.45 * δ₁ * P.height) := by have := L_ge_82 hh30; linarith
  have hC2 := c2_of_p8 hε1 hh0 hl1' hD0 hL0 hT hB
  have : (1 + ε) * D ≤ (1 + ε) * R := mul_le_mul_of_nonneg_left hDR (by linarith)
  linarith

/-- The `j`-invariants of Proposition 2.1 have `h^non(j) ≤ log 125`. -/
theorem hnon_excJ_le {j : ℚ} (hj : j ∈ excJ) : hnon j ≤ Real.log 125 := by
  rw [hnon_eq_log_den]
  have hden : j.den ≤ 125 := by
    rcases hj with rfl | rfl | rfl | rfl
    · have e : (488095744 / 125 : ℚ) = Rat.divInt 488095744 125 := by
        rw [Rat.divInt_eq_div]; push_cast; rfl
      have := Rat.den_dvd 488095744 125
      rw [← e] at this
      have := Int.le_of_dvd (by norm_num) this
      exact_mod_cast this
    · have e : (1556068 / 81 : ℚ) = Rat.divInt 1556068 81 := by
        rw [Rat.divInt_eq_div]; push_cast; rfl
      have := Rat.den_dvd 1556068 81
      rw [← e] at this
      have := Int.le_of_dvd (by norm_num) this
      omega
    · simp
    · simp
  exact Real.log_le_log (by exact_mod_cast j.den_pos) (by exact_mod_cast hden)

/-- **The inputs of §5 for every curve `E_{a,b,c}` of Theorem 5.3** (nonzero `a, b, c ∈ ℚ`,
`a + b + c = 0`; not every elliptic curve over `ℚ`), with `h = h^non(j)` and
`R = log rad_ℚ(a, b, c)` substituted into `Cor52Input`. -/
def Sec5Inputs : Prop :=
  ∀ (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0),
    Cor52Input (hnon (@WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc)))
      (Real.log (radQ a b c)) (@WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc))

/-- **Theorem 5.3 (i) over `ℚ` from the inputs** (p. 43: "(i) follows immediately from
Corollary 5.2 … Remark 1.10.1, and the various definitions"): for `0 < ε ≤ 1`. -/
theorem thm53i_of_inputs (PNT : PNT_lower) (IN : Sec5Inputs) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) : Thm53i_Q ε := by
  intro a b c ha hb hc habc
  set j := @WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc) with hjdef
  by_cases hlt : hnon j < h1 ε
  · exact le_trans (by linarith) (le_max_right _ _)
  push Not at hlt
  have hj : j ∉ excJ := by
    intro hmem
    have h1 := hnon_excJ_le hmem
    have h2 : Real.log 125 ≤ 125 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h3 := le_of_h1_le hε hε1 hlt
    linarith
  have := cor52_C2 PNT hε hε1 hj hlt (IN a b c ha hb hc habc)
  exact le_trans (by linarith) (le_max_left _ _)

/-- **The chain**: `PNT_lower` + `Sec5Inputs` ⇒ Theorem 5.3 (i) (`ε = 1`) ⇒ (ii) ⇒ Corollary 5.8. -/
theorem cor58_of_inputs (PNT : PNT_lower) (IN : Sec5Inputs) {p : ℕ} (hp : p.Prime)
    (hpbig : (1.615 * 10 ^ 14 : ℝ) < p) {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ p + y ^ p ≠ z ^ p :=
  cor58_of_thm53i (thm53i_of_inputs PNT IN one_pos le_rfl) hp hpbig hx hy hz

end ExpEst
