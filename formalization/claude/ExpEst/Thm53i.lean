import ExpEst.Thm53

/-!
# Theorem 5.3 (i) for `L = ℚ`: the objects in its statement

* `hnon x = h^non(x) = ∑_{v ∈ V(ℚ)^non} log max{|x|_v, 1}` (Definition 1.1 (i), `[ℚ:ℚ] = 1`),
  with the finite places of `ℚ` indexed by the primes `q` and `|x|_q = padicNorm q x`;
* `Eabc a b c` is the Weierstrass curve `y² = x(x - 1)(x + a/c)` over `ℚ`
  (`a₂ = a/c - 1`, `a₄ = -a/c`, `a₁ = a₃ = a₆ = 0`);
* its `j`-invariant is Mathlib's `WeierstrassCurve.j`, which needs the instance
  `(Eabc a b c).IsElliptic` (proved below for nonzero `a, b, c` with `a + b + c = 0`).

`Thm53i_Q ε` is Theorem 5.3 (i) for `L = ℚ` (`d = 1`, `Δ_ℚ = 1`), first inequality.
-/

namespace ExpEst

open Real Height

/-- `h^non(x) = ∑_{q prime} log max{|x|_q, 1}` (Definition 1.1 (i) for `F = ℚ`). -/
noncomputable def hnon (x : ℚ) : ℝ :=
  ∑ᶠ q : Nat.Primes, Real.log (max ((padicNorm (q : ℕ) x : ℚ) : ℝ) 1)

/-- The curve `E_{a,b,c} : y² = x(x - 1)(x + a/c)`. -/
def Eabc (a _b c : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a / c - 1
  a₃ := 0
  a₄ := -(a / c)
  a₆ := 0

theorem Eabc_Δ (a b c : ℚ) (hc : c ≠ 0) (habc : a + b + c = 0) :
    (Eabc a b c).Δ = 16 * a ^ 2 * b ^ 2 / c ^ 4 := by
  have hb : b = -a - c := by linarith
  subst hb
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, Eabc]
  field_simp
  ring

theorem Eabc_c₄ (a b c : ℚ) (hc : c ≠ 0) (habc : a + b + c = 0) :
    (Eabc a b c).c₄ = 16 * (a ^ 2 + a * b + b ^ 2) / c ^ 2 := by
  have hb : b = -a - c := by linarith
  subst hb
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, Eabc]
  field_simp
  ring

/-- `E_{a,b,c}` is an elliptic curve when `a, b, c` are nonzero and `a + b + c = 0`. -/
theorem Eabc_isElliptic {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) :
    (Eabc a b c).IsElliptic := by
  refine ⟨?_⟩
  rw [Eabc_Δ a b c hc habc, isUnit_iff_ne_zero]
  positivity

/-- **Theorem 5.3 (i)** of the paper for `L = ℚ` (`d = 1`, `Δ_ℚ = 1`), first inequality:
`(1/6)·h^non(j(E_{a,b,c})) ≤ max{(1 + ε)·log rad_ℚ(a, b, c), (1/6)·h₁(ε)}`. -/
def Thm53i_Q (ε : ℝ) : Prop :=
  ∀ (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0),
    (1 / 6 : ℝ) * hnon (@WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc)) ≤
      max ((1 + ε) * Real.log (radQ a b c)) ((1 / 6 : ℝ) * h1 ε)

/-- `j(E_{a,b,c}) = 2^8 (a² + ab + b²)³ / (abc)²`. -/
theorem j_Eabc {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) :
    @WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc) =
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a * b * c) ^ 2 := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', Eabc_Δ a b c hc habc, Eabc_c₄ a b c hc habc]
  field_simp
  ring

/-- `max{|x|_q, 1} = q^{v_q(den x)}`. -/
theorem max_padicNorm_one (q : ℕ) [hq : Fact q.Prime] (x : ℚ) :
    max ((padicNorm q x : ℚ) : ℝ) 1 = (q : ℝ) ^ (padicValNat q x.den) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_lt.le
  rw [padicNorm.eq_zpow_of_nonzero hx]
  unfold padicValRat
  by_cases hd : q ∣ x.den
  · have hn : ¬ q ∣ x.num.natAbs := by
      intro hn
      have := Nat.dvd_gcd hn hd
      rw [x.reduced.gcd_eq_one] at this
      exact hq.out.one_lt.ne' (Nat.dvd_one.mp this)
    have h0 : padicValInt q x.num = 0 := by
      rw [padicValInt]
      exact padicValNat.eq_zero_of_not_dvd hn
    rw [h0]
    simp only [CharP.cast_eq_zero, zero_sub, neg_neg]
    rw [Rat.cast_zpow, Rat.cast_natCast, zpow_natCast]
    exact max_eq_left (one_le_pow₀ hq1)
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    simp only [CharP.cast_eq_zero, sub_zero, pow_zero]
    apply max_eq_right
    have hv : (0 : ℤ) ≤ padicValInt q x.num := by positivity
    rw [Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_le_one_of_nonpos₀ hq1 (by omega)

/-- Over `ℚ`, `h^non(x) = log (den x)`. -/
theorem hnon_eq_log_den (x : ℚ) : hnon x = Real.log x.den := by
  set n := x.den with hn
  have hn0 : n ≠ 0 := x.den_nz
  set g : Nat.Primes → ℝ := fun q => (n.factorization (q : ℕ) : ℝ) * Real.log (q : ℕ) with hg
  have hfg : (fun q : Nat.Primes => Real.log (max ((padicNorm (q : ℕ) x : ℚ) : ℝ) 1)) = g := by
    funext q
    haveI := Fact.mk q.2
    rw [max_padicNorm_one, Real.log_pow, hg]
    simp only
    rw [Nat.factorization_def n q.2]
  set s : Finset Nat.Primes := n.primeFactors.subtype Nat.Prime with hs
  have hsupp : Function.support g ⊆ (s : Set Nat.Primes) := by
    intro q hq
    rw [Function.mem_support] at hq
    rw [hs, Finset.mem_coe]
    apply (Finset.mem_subtype (p := Nat.Prime) (s := n.primeFactors) (a := q)).mpr
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h0
    apply hq
    simp [hg, h0]
  rw [hnon, hfg, finsum_eq_sum_of_support_subset g hsupp, Real.log_nat_eq_sum_factorization n,
    Finsupp.sum, Nat.support_factorization, hs]
  change ∑ q ∈ (Finset.subtype Nat.Prime n.primeFactors : Finset (Subtype Nat.Prime)),
    (fun p : ℕ => (n.factorization p : ℝ) * Real.log p) (q : ℕ) = _
  rw [Finset.sum_subtype_eq_sum_filter (f := fun p : ℕ => (n.factorization p : ℝ) * Real.log p)]
  congr 1
  ext q
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  tauto

end ExpEst
