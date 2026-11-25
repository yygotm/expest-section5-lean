import ExpEstL3
import Mathlib.Data.Nat.Prime.Infinite

namespace ExpEstL3
open Real Finset ExpEstL2
noncomputable section

/-- An arithmetic model for testing the interface: on ℚ the prime
    factorization of the reduced denominator gives h_non exactly. -/
def denominatorData (j : ℚ) : LocalData where
  places := j.den.primeFactors
  p := id
  n := j.den.factorization
  f := fun _ => 1
  degree := 1
  deg_pos := by decide
  deg_le := by norm_num [δ]
  prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  npos := fun _ hp => (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
    j.den_ne_zero (Nat.dvd_of_mem_primeFactors hp)
  fpos := by simp
  fibre := by intro l; by_cases hl : l∈j.den.primeFactors <;> simp [Finset.filter_eq',hl]

theorem denominator_height (j : ℚ) : (denominatorData j).height=hNon j := by
  simp only [LocalData.height, LocalData.weight,denominatorData, Nat.cast_one,mul_one,div_one,id_eq,hNon]
  exact (log_nat_eq_sum_factorization j.den).symm

private theorem restrict_le (T : LocalData) (l : ℕ) : 0≤T.restricted l ∧ T.restricted l≤T.height := by
  constructor
  · exact div_nonneg (sum_nonneg fun v _ => T.weight_nonneg v) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right
      (sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun v _ _ => T.weight_nonneg v) (Nat.cast_nonneg _)

/-- If the simple height bound already holds at a point, all seven
    projected inputs have an explicit model there. The truth values here
    interpret interface predicates, not Galois representations. -/
theorem external_witness (D : QTriple) (hs : hNon D.curve.j/6≤log D.radical) :
    ∃ M, External D M := by
  let T := denominatorData D.curve.j
  let B := log (D.radical:ℝ)
  let ready := fun l : ℕ => l.Prime ∧ (10^15:ℝ)≤l ∧ (∀ v∈T.places, ¬l∣T.n v) ∧ T.Away l
  let M : ArithmeticData := ⟨T,fun _ => B,¬exceptionalJ D.curve.j,fun _ => False,ready,ready⟩
  have hB : 0≤B := log_nonneg (by exact_mod_cast rad_pos D.primitive.product)
  refine ⟨M,denominator_height _,Classical.not_not.mp,by simp [M],
    fun l hp hbig hnd _ ha => ⟨hp,hbig,hnd,ha⟩,fun _ _ _ _ _ hsl => hsl,
    fun _ _ => ⟨hB,le_rfl⟩,?_⟩
  intro l hready _hlarge
  change ready l at hready
  apply (theta51_iff (T.restricted_pos hready.2.2.2) (show (0:ℝ)<l by exact_mod_cast hready.1.pos)).mpr
  change (1-12/(l:ℝ)^2)*(T.restricted l/6) ≤ (1+12/(l:ℝ))*B+4.08803*δ*l
  have ⟨hq,hupper⟩ := restrict_le T l
  have hB' : T.height/6≤B := (denominator_height D.curve.j) ▸ hs
  calc
    _ ≤ 1*(T.restricted l/6) := mul_le_mul_of_nonneg_right (by have := div_nonneg (by norm_num : (0:ℝ)≤12) (sq_nonneg (l:ℝ)); linarith only [this])
      (div_nonneg hq (by norm_num))
    _ ≤ B := by linarith only [hupper,hB']
    _ ≤ (1+12/(l:ℝ))*B+4.08803*δ*l := by
      have hy : 0≤(12/(l:ℝ))*B := mul_nonneg (by positivity) hB
      have hz : 0≤4.08803*δ*(l:ℝ) := by positivity
      linarith only [hy,hz]

private def primeTriple (p : ℕ) (hp : p.Prime) : Primitive where
  a := p
  b := 1
  c := -((p:ℤ)+1)
  ha := by exact_mod_cast hp.ne_zero
  hb := by decide
  hc := by omega
  sum := by ring
  cop := isCoprime_one_right

private lemma primeTriple_product {p : ℕ} (hp : p.Prime) :
    (primeTriple p hp).product = p*(p+1) := by
  change ((p:ℤ)*1*(-((p:ℤ)+1))).natAbs=_
  rw [mul_one,Int.natAbs_mul,Int.natAbs_neg,← Nat.cast_add_one]
  rfl

private theorem upper_den (T : Primitive) : T.asQ.curve.j.den ≤ T.product^2 := by
  let A := 256*(T.a^2+T.a*T.b+T.b^2)^3
  let C := (T.a*T.b*T.c)^2
  have he : T.asQ.curve.j=Rat.divInt A C := by
    rw [Rat.divInt_eq_div,T.asQ.j_formula]
    simp [Primitive.asQ,A,C]
  have hd := Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd A C)
  rw [he]
  apply Nat.le_of_dvd (pow_pos T.product_pos _)
  simpa [C,Primitive.product,Int.natAbs_pow] using hd

private theorem primeTriple_good {p : ℕ} (hp : p.Prime) :
    hNon (primeTriple p hp).asQ.curve.j/6 ≤ log (primeTriple p hp).asQ.radical := by
  let T := primeTriple p hp
  have hpP : p∣T.product := by rw [show T.product=p*(p+1) from primeTriple_product hp]; exact dvd_mul_right .. 
  have hR : p≤T.asQ.radical := by
    rw [T.radical_asQ]
    exact Nat.le_of_dvd (rad_pos _) (Finset.dvd_prod_of_mem (fun q : ℕ => q)
      (hp.mem_primeFactors hpP T.product_pos.ne'))
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hd := upper_den T
  have hp2 := hp.two_le
  have hprod : T.product ≤ p^3 := by
    rw [show T.product=p*(p+1) from primeTriple_product hp, pow_succ]
    rw [mul_comm p (p+1)]
    exact Nat.mul_le_mul_right p (by nlinarith [Nat.sub_add_cancel hp2])
  have hden : (T.asQ.curve.j.den:ℝ) ≤ (p:ℝ)^6 := by
    exact_mod_cast hd.trans ((Nat.pow_le_pow_left hprod 2).trans_eq (by ring))
  have H := log_le_log (by exact_mod_cast T.asQ.curve.j.den_pos) hden
  rw [log_pow] at H
  have hh : hNon T.asQ.curve.j/6 ≤ log (p:ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<6)).mpr
    rw [mul_comm]; exact H
  exact hh.trans
    (log_le_log hp0 (by exact_mod_cast hR))

/-- For every real cutoff there is an actual rational triple above it for
    which all seven numerical interface assumptions are jointly inhabited.
    No prime-number-theorem hypothesis enters this existence proof. -/
theorem arbitrarily_large_models (B : ℝ) :
    ∃ (D : QTriple) (M : ArithmeticData), B < hNon D.curve.j ∧ External D M := by
  let x := exp (B/2+4*log 2+1)
  obtain ⟨p,hpN,hp⟩ := Nat.exists_infinite_primes ⌈x⌉₊
  let T := primeTriple p hp
  have hx : x ≤ (p:ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast hpN)
  have hlog := (le_log_iff_exp_le (by exact_mod_cast hp.pos : (0:ℝ)<p)).mpr hx
  have pp : p≤T.product := by rw [show T.product=p*(p+1) from primeTriple_product hp]; nlinarith
  have H := log_le_log (by exact_mod_cast hp.pos : (0:ℝ)<p) (show (p:ℝ)≤T.product by exact_mod_cast pp)
  have hh := product_log_bound T
  obtain ⟨M,hm⟩ := external_witness T.asQ (primeTriple_good hp)
  refine ⟨T.asQ,M,?_,hm⟩
  change B/2+4*log 2+1 ≤ log (p:ℝ) at hlog
  linarith only [hlog,H,hh]

/-- With the PNT input, the example really enters the large branch:
    the prime, an away place, and the positive restricted height coexist. -/
theorem active_example (pnt : PrimeEstimate) {ε : ℝ} (he : 0<ε) (hε : ε≤1) :
    ∃ (D : QTriple) (M : ArithmeticData) (l : ℕ), External D M ∧
      parameter D ∉ exceptional (hOne ε) ∧ M.localData.Eligible l ∧
      M.initialData l ∧ 0<M.localData.restricted l := by
  obtain ⟨D,M,H,I⟩ := arbitrarily_large_models (hOne ε)
  have out := fun hx => (not_le.mpr H) ((mem_exceptional D).mp hx)
  obtain ⟨l,E,_,ha,_,hi,_⟩ := corollary52 pnt I he hε out
  exact ⟨D,M,l,I,out,E,hi,M.localData.restricted_pos ha⟩

#print axioms arbitrarily_large_models
#print axioms active_example
end
end ExpEstL3
