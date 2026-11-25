import ExpEst.Cor58

/-!
# Theorem 5.3 (ii) for `L = ℚ`, `ε = 1`, stated with heights and places

This file states the hypothesis of Corollary 5.8 in the paper's own terms:

* `H_ℚ(a, b, c) = ∏_{v ∈ V(ℚ)} max{|a|_v, |b|_v, |c|_v}` is Mathlib's
  `Height.mulHeight ![a, b, c]` (product over the archimedean place and all finite places of ℚ);
* `I_ℚ(a, b, c)` is the set of primes `q` for which `|a|_q, |b|_q, |c|_q` are not all equal
  (i.e. take at least two values), and `rad_ℚ(a, b, c) = ∏_{q ∈ I_ℚ(a,b,c)} q`
  (`#(ℤ/q) = q`; `Δ_ℚ = 1`);
* `h₁(1) = 3.4·10^30`, exponent `3(1 + ε)/2 = 3`, factor `2^(5d/2) = 2^(5/2)`.

We prove `Thm53ii_Q → Thm53ii_Q_int`, so Corollary 5.8 follows from `Thm53ii_Q`.
-/

namespace ExpEst

open Real Height

/-- `rad_ℚ(a, b, c)`: product of the primes `q` at which `|a|_q, |b|_q, |c|_q` are not all equal. -/
noncomputable def radQ (a b c : ℚ) : ℝ :=
  ∏ᶠ q : Nat.Primes,
    if padicNorm (q : ℕ) a = padicNorm (q : ℕ) b ∧ padicNorm (q : ℕ) b = padicNorm (q : ℕ) c
    then 1 else ((q : ℕ) : ℝ)

/-- **Theorem 5.3 (ii)** of the paper for `L = ℚ`, `ε = 1` (first inequality, `max` form). -/
def Thm53ii_Q : Prop :=
  ∀ a b c : ℚ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 →
    mulHeight ![a, b, c] ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) (radQ a b c ^ 3)

/-- For integers, `rad_ℚ(a, b, c) ≤ rad(abc)`. -/
theorem radQ_le_rad (a b c : ℤ) (habc : a * b * c ≠ 0) :
    radQ a b c ≤ (rad (a * b * c) : ℝ) := by
  set n := (a * b * c).natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr habc
  set f : Nat.Primes → ℝ := fun q =>
    if padicNorm (q : ℕ) (a : ℚ) = padicNorm (q : ℕ) (b : ℚ) ∧
        padicNorm (q : ℕ) (b : ℚ) = padicNorm (q : ℕ) (c : ℚ)
    then 1 else ((q : ℕ) : ℝ) with hf
  set s : Finset Nat.Primes := n.primeFactors.subtype Nat.Prime with hs
  have hsupp : Function.mulSupport f ⊆ (s : Set Nat.Primes) := by
    intro q hq
    rw [Function.mem_mulSupport] at hq
    rw [hs, Finset.mem_coe]
    apply (Finset.mem_subtype (p := Nat.Prime) (s := n.primeFactors) (a := q)).mpr
    rw [Nat.mem_primeFactors]
    refine ⟨q.2, ?_, hn0⟩
    by_contra hqn
    apply hq
    haveI := Fact.mk q.2
    have hqZ : ¬ ((q : ℕ) : ℤ) ∣ a * b * c := fun h => hqn (Int.natCast_dvd.mp h)
    have ha : ¬ ((q : ℕ) : ℤ) ∣ a := fun h => hqZ (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
    have hb : ¬ ((q : ℕ) : ℤ) ∣ b := fun h => hqZ (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
    have hc : ¬ ((q : ℕ) : ℤ) ∣ c := fun h => hqZ (dvd_mul_of_dvd_right h _)
    have e1 := (padicNorm.int_eq_one_iff (p := (q : ℕ)) a).mpr ha
    have e2 := (padicNorm.int_eq_one_iff (p := (q : ℕ)) b).mpr hb
    have e3 := (padicNorm.int_eq_one_iff (p := (q : ℕ)) c).mpr hc
    simp [hf, e1, e2, e3]
  have hrad : radQ a b c = ∏ q ∈ s, f q := by
    rw [radQ]
    exact finprod_eq_prod_of_mulSupport_subset f hsupp
  rw [hrad]
  have hle : ∏ q ∈ s, f q ≤ ∏ q ∈ s, (((q : Nat.Primes) : ℕ) : ℝ) := by
    apply Finset.prod_le_prod
    · intro q _
      simp only [hf]
      split_ifs <;> positivity
    · intro q _
      simp only [hf]
      split_ifs
      · exact_mod_cast q.2.one_lt.le
      · exact le_rfl
  refine hle.trans (le_of_eq ?_)
  rw [rad, Nat.cast_prod, ← hn, hs]
  change ∏ q ∈ (Finset.subtype Nat.Prime n.primeFactors : Finset (Subtype Nat.Prime)),
    (fun q : ℕ => (q : ℝ)) (q : ℕ) = _
  rw [Finset.prod_subtype_eq_prod_filter (f := fun q : ℕ => (q : ℝ))]
  congr 1
  ext q
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  tauto

/-- `gcd(a, b, c) = 1` from `IsCoprime a b`. -/
theorem gcd_fin3_eq_one {a b c : ℤ} (hab : IsCoprime a b) :
    Finset.univ.gcd ![a, b, c] = 1 := by
  set g := Finset.univ.gcd ![a, b, c] with hg
  have ha : g ∣ a := Finset.gcd_dvd (s := Finset.univ) (f := ![a, b, c]) (Finset.mem_univ 0)
  have hb : g ∣ b := Finset.gcd_dvd (s := Finset.univ) (f := ![a, b, c]) (Finset.mem_univ 1)
  have hu : IsUnit g := hab.isUnit_of_dvd' ha hb
  have hn : normalize g = g := Finset.normalize_gcd
  rw [← hn]
  exact normalize_eq_one.mpr hu

/-- For coprime integers, `max{|a|, |b|, |c|} ≤ H_ℚ(a, b, c)`. -/
theorem max_abs_le_mulHeight {a b c : ℤ} (hab : IsCoprime a b) :
    max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|) ≤ mulHeight ![(a : ℚ), (b : ℚ), (c : ℚ)] := by
  have hcomp : ![(a : ℚ), (b : ℚ), (c : ℚ)] = ((↑) : ℤ → ℚ) ∘ ![a, b, c] := by
    ext i
    fin_cases i <;> rfl
  rw [hcomp, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (gcd_fin3_eq_one hab)]
  have hb : BddAbove (Set.range fun i => |![a, b, c] i|) := Set.finite_range _ |>.bddAbove
  have h0 : |a| ≤ ⨆ i, |![a, b, c] i| := le_ciSup hb 0
  have h1 : |b| ≤ ⨆ i, |![a, b, c] i| := le_ciSup hb 1
  have h2 : |c| ≤ ⨆ i, |![a, b, c] i| := le_ciSup hb 2
  have h0' : |(a : ℝ)| ≤ ((⨆ i, |![a, b, c] i| : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : |(b : ℝ)| ≤ ((⨆ i, |![a, b, c] i| : ℤ) : ℝ) := by exact_mod_cast h1
  have h2' : |(c : ℝ)| ≤ ((⨆ i, |![a, b, c] i| : ℤ) : ℝ) := by exact_mod_cast h2
  exact max_le h0' (max_le h1' h2')

/-- The paper's Theorem 5.3 (ii) (`L = ℚ`, `ε = 1`) implies the integral form used in
`cor58`. -/
theorem thm53ii_Q_to_int (H : Thm53ii_Q) : Thm53ii_Q_int := by
  intro a b c ha hb hc habc hab
  have hH := H a b c (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
    (by exact_mod_cast habc)
  have hrad := radQ_le_rad a b c (mul_ne_zero (mul_ne_zero ha hb) hc)
  have hrad0 : 0 ≤ radQ a b c := by
    rw [radQ]
    apply finprod_nonneg
    intro q
    split_ifs <;> positivity
  calc max |(a : ℝ)| (max |(b : ℝ)| |(c : ℝ)|) ≤ mulHeight ![(a : ℚ), (b : ℚ), (c : ℚ)] :=
        max_abs_le_mulHeight hab
    _ ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) (radQ a b c ^ 3) := hH
    _ ≤ 2 ^ ((5 : ℝ) / 2) * max (exp (h1 1 / 4)) ((rad (a * b * c) : ℝ) ^ 3) := by
        gcongr

/-- **Corollary 5.8** from Theorem 5.3 (ii) as stated in the paper (`L = ℚ`, `ε = 1`). -/
theorem cor58_Q (H : Thm53ii_Q) {p : ℕ} (hp : p.Prime) (hpbig : (1.615 * 10 ^ 14 : ℝ) < p)
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ p + y ^ p ≠ z ^ p :=
  cor58 (thm53ii_Q_to_int H) hp hpbig hx hy hz

end ExpEst
