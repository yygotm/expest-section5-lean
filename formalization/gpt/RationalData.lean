import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ExpEstL2
open Real

structure QTriple where
  a : ℚ
  b : ℚ
  c : ℚ
  ha : a ≠ 0
  hb : b ≠ 0
  hc : c ≠ 0
  sum : a + b + c = 0

structure Primitive where
  a : ℤ
  b : ℤ
  c : ℤ
  ha : a ≠ 0
  hb : b ≠ 0
  hc : c ≠ 0
  sum : a + b + c = 0
  cop : IsCoprime a b

def Primitive.asQ (T : Primitive) : QTriple :=
  ⟨T.a,T.b,T.c,by exact_mod_cast T.ha,by exact_mod_cast T.hb,by exact_mod_cast T.hc,
    by exact_mod_cast T.sum⟩

/-- Projective normalization with positive second coordinate. -/
def QTriple.primitive (D : QTriple) : Primitive := by
  let q := D.a / D.b
  have hn : q.num ≠ 0 := by simpa [q] using div_ne_zero D.ha D.hb
  have hd : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.num:ℚ)/q.den = D.a/D.b := Rat.num_div_den q
  have hdq : (q.den:ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hcross := (div_eq_div_iff hdq D.hb).mp hq
  refine ⟨q.num,q.den,-(q.num+q.den),hn,hd,?_,by ring,?_⟩
  · intro h
    have eqz : (q.num:ℚ)+(q.den:ℚ)=0 := by exact_mod_cast (show q.num+(q.den:ℤ)=0 by omega)
    have dz : D.a+D.b=0 := by
      apply mul_right_cancel₀ hdq
      linear_combination -hcross + D.b*eqz
    exact D.hc (by linarith [D.sum])
  · exact Int.isCoprime_iff_nat_coprime.mpr (by simpa using q.reduced)

lemma QTriple.scale_primitive (D : QTriple) :
    ∃ k : ℚ, k ≠ 0 ∧ D.a=k*D.primitive.a ∧ D.b=k*D.primitive.b ∧ D.c=k*D.primitive.c := by
  let q := D.a/D.b
  have hd : (q.den:ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  have cross := (div_eq_div_iff hd D.hb).mp (show (q.num:ℚ)/q.den = D.a/D.b from Rat.num_div_den q)
  have ha : D.a=(D.b/q.den)*q.num := by rw [div_mul_eq_mul_div, eq_div_iff hd]; linarith
  have hb : D.b=(D.b/q.den)*q.den := (div_mul_cancel₀ _ hd).symm
  refine ⟨D.b/q.den, div_ne_zero D.hb hd, ha, hb, ?_⟩
  change D.c=(D.b/q.den)*((-(q.num+(q.den:ℤ)):ℤ):ℚ)
  push_cast
  linarith only [ha,hb,D.sum]

def Primitive.product (T : Primitive) : ℕ := (T.a*T.b*T.c).natAbs
def Primitive.height (T : Primitive) : ℕ := max T.a.natAbs (max T.b.natAbs T.c.natAbs)
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
def QTriple.height (D : QTriple) : ℕ := D.primitive.height
def QTriple.radical (D : QTriple) : ℕ := rad D.primitive.product

/-- y² = x(x-1)(x+a/c). -/
def QTriple.curve (D : QTriple) : WeierstrassCurve ℚ :=
  ⟨0, D.a/D.c-1, 0, -(D.a/D.c), 0⟩

lemma QTriple.discriminant (D : QTriple) :
    D.curve.Δ = 16*(D.a/D.c)^2*(D.b/D.c)^2 := by
  have hb : D.b = -(D.a+D.c) := by linarith [D.sum]
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  rw [hb]
  field_simp [D.hc]
  ring

instance (D : QTriple) : D.curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by
    rw [D.discriminant]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (div_ne_zero D.ha D.hc)))
      (pow_ne_zero _ (div_ne_zero D.hb D.hc)))⟩

lemma QTriple.j_formula (D : QTriple) :
    D.curve.j = 256*(D.a^2+D.a*D.b+D.b^2)^3 / (D.a*D.b*D.c)^2 := by
  have hc : D.c = -(D.a+D.b) := by linarith [D.sum]
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', D.discriminant]
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [D.ha,D.hb,D.hc]
  rw [hc]
  ring

lemma QTriple.j_primitive (D : QTriple) : D.curve.j = D.primitive.asQ.curve.j := by
  obtain ⟨k,hk,ha,hb,hc⟩ := D.scale_primitive
  rw [D.j_formula,D.primitive.asQ.j_formula]
  change _ = 256*((D.primitive.a:ℚ)^2+_*_+(D.primitive.b:ℚ)^2)^3 / _^2
  simp only [Primitive.asQ]
  conv_lhs => rw [ha,hb,hc]
  field_simp [hk]

/-- Definition 1.1(i) over ℚ. The local identity below identifies the support. -/
noncomputable def hNon (q : ℚ) : ℝ := log q.den
noncomputable def torNon (q : ℚ) : ℝ := (hNon q+hNon q⁻¹)/2

lemma local_height (q : ℚ) {p : ℕ} (hp : p.Prime) :
    log (max (padicNorm p q : ℝ) 1) = q.den.factorization p * log p := by
  by_cases hq : q=0
  · subst q; simp
  rw [padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast]
  change log (max ((p:ℝ)^(-((padicValNat p q.num.natAbs:ℤ) - (padicValNat p q.den:ℤ)))) 1) = _
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp]
  have h1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
  by_cases h : p∣q.den
  · have hn : ¬ p∣q.num.natAbs := fun h' => Nat.not_coprime_of_dvd_of_dvd hp.one_lt h' h q.reduced
    rw [Nat.factorization_eq_zero_of_not_dvd hn]
    simp only [Nat.cast_zero,zero_sub,neg_neg,zpow_natCast,max_eq_left (one_le_pow₀ h1),log_pow]
  · rw [Nat.factorization_eq_zero_of_not_dvd h]
    simp only [Nat.cast_zero, sub_zero, zero_mul]
    rw [max_eq_right (zpow_le_one_of_nonpos₀ h1 (by exact neg_nonpos.mpr (Int.natCast_nonneg _))),log_one]

lemma hNon_eq_finite_sum (q : ℚ) :
    hNon q = ∑ p ∈ q.den.primeFactors, log (max (padicNorm p q : ℝ) 1) := by
  rw [hNon, log_nat_eq_sum_factorization]
  apply Finset.sum_congr rfl
  intro p hp
  exact (local_height q (Nat.prime_of_mem_primeFactors hp)).symm

lemma local_height_outside (q : ℚ) {p : ℕ} (hp : p.Prime) (h : p ∉ q.den.primeFactors) :
    log (max (padicNorm p q : ℝ) 1) = 0 := by
  rw [local_height q hp, Nat.factorization_eq_zero_of_not_dvd (fun hd => h (hp.mem_primeFactors hd q.den_ne_zero)), Nat.cast_zero, zero_mul]

end ExpEstL2
