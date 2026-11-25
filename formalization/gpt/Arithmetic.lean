import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

namespace ExpEst
open Finset
private def weighted (r q : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range n, ((i : ℤ) + 1) * r ^ (n - 1 - i) * q ^ i

private lemma weighted_succ (r q : ℤ) (n : ℕ) :
    weighted r q (n+1) = r * weighted r q n + (n+1 : ℤ) * q^n := by
  simp only [weighted, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [show n - i = n - 1 - i + 1 by omega, pow_succ]
  ring

private lemma weighted_identity (r q : ℤ) (n : ℕ) :
    (r-q)^2 * weighted r q n =
      r^(n+1) - ((n:ℤ)+1)*r*q^n + (n:ℤ)*q^(n+1) := by
  induction n with
  | zero => simp [weighted]
  | succ n ih =>
    rw [weighted_succ, Nat.cast_succ, pow_succ r (n+1), pow_succ q (n+1), pow_succ q n]
    rw [pow_succ q n] at ih
    linear_combination r * ih

/-- Lemma 5.5, with exact integer division. -/
theorem lemma55 (r s : ℤ) (p : ℕ) (hp : 3 ≤ p) (ho : Odd p) (hrs : r+s ≠ 0) :
    (r^p+s^p) / (r+s) = p*s^(p-1) - (r+s) *
      ∑ i ∈ range (p-1), (-1 : ℤ)^(i+1)*((i:ℤ)+1)*r^(p-2-i)*s^i := by
  have hn : p-1+1 = p := by omega
  have he : Even (p-1) := Nat.Odd.sub_odd ho odd_one
  have hi := weighted_identity r (-s) (p-1)
  rw [hn, ho.neg_pow, he.neg_pow, sub_neg_eq_add, Nat.cast_sub (by omega : 1 ≤ p)] at hi
  have hsum : (∑ i ∈ range (p-1), (-1 : ℤ)^(i+1)*((i:ℤ)+1)*r^(p-2-i)*s^i) =
      -weighted r (-s) (p-1) := by
    rw [weighted, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [show -s = (-1)*s by ring, mul_pow, pow_succ]
    have : p-1-1=p-2 := by omega
    rw [this]
    ring
  rw [hsum]
  apply Int.ediv_eq_of_eq_mul_right hrs
  have hs : s^p = s^(p-1)*s := by nth_rw 1 [← hn]; exact pow_succ _ _
  rw [hs] at hi ⊢
  push_cast at hi
  linear_combination -hi

/-- The geometric sum is the exact signed Fermat quotient. -/
def quotient (r s : ℤ) (p : ℕ) : ℤ := ∑ i ∈ range p, r^i * (-s)^(p-1-i)

lemma factor (r s : ℤ) {p : ℕ} (ho : Odd p) :
    (r+s)*quotient r s p = r^p+s^p := by
  simpa [quotient, mul_comm (r+s), ho.neg_pow] using geom_sum₂_mul r (-s) p

lemma quotient_eq_div {r s : ℤ} {p : ℕ} (ho : Odd p) (h : r+s ≠ 0) :
    quotient r s p = (r^p+s^p)/(r+s) := by
  rw [← factor r s ho, Int.mul_ediv_cancel_left _ h]

/-- The denominator in 5.6 is nonzero for every triple in the paper. -/
lemma sum_ne_zero {r s t : ℤ} {p : ℕ} (ho : Odd p) (ht : t≠0)
    (he : r^p+s^p+t^p=0) : r+s≠0 := by
  intro h
  rw [show r = -s by omega, ho.neg_pow] at he
  exact pow_ne_zero p ht (by omega)

private lemma prime_coprime_test {a b : ℤ}
    (h : ∀ l : ℕ, l.Prime → (l:ℤ) ∣ a → (l:ℤ) ∣ b → False) : IsCoprime a b :=
  Int.isCoprime_iff_nat_coprime.mpr (Nat.coprime_of_dvd fun l hl ha hb =>
    h l hl (Int.natCast_dvd.mpr ha) (Int.natCast_dvd.mpr hb))

lemma lemma56i {r s : ℤ} {p l : ℕ} (hp : p.Prime) (hl : l.Prime) (hrs : IsCoprime r s)
    (hd : (l:ℤ) ∣ r+s) (hq : (l:ℤ) ∣ quotient r s p) : l = p := by
  have hL := Nat.prime_iff_prime_int.mp hl
  have h := (dvd_geom_sum₂_iff_of_dvd_sub' (x := r) (y := -s) (n := p)
    (by simpa using hd : (l:ℤ) ∣ r - -s)).mp hq
  rcases hL.dvd_or_dvd h with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hl hp).mp (Int.natCast_dvd_natCast.mp h)
  · have hr := hL.dvd_of_dvd_pow h
    have hs : (l:ℤ) ∣ s := by simpa using dvd_sub hd hr
    exact (hL.not_unit (hrs.isUnit_of_dvd' hr hs)).elim

private lemma combine_roots {a b c : ℤ} {p : ℕ} (ho : Odd p) (hc : IsCoprime a b)
    (h : a*b=(-c)^p) : ∃ u v : ℤ, a=u^p ∧ b=v^p ∧ c = -(u*v) := by
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hc ho h
  rw [hu, hv, ← mul_pow] at h
  have e := ho.strictMono_pow.injective h
  exact ⟨u,v,hu,hv,by omega⟩

lemma lemma56ii {r s t : ℤ} {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (hrs : IsCoprime r s)
    (he : r^p+s^p+t^p=0) (ht : ¬ (p:ℤ) ∣ t) :
    IsCoprime (r+s) (quotient r s p) ∧
      ∃ u v : ℤ, r+s=u^p ∧ quotient r s p=v^p ∧ t = -(u*v) := by
  have ho := hp.odd_of_ne_two (by omega)
  have hprod : (r+s)*quotient r s p=(-t)^p := by rw [factor _ _ ho,ho.neg_pow]; omega
  have hc : IsCoprime (r+s) (quotient r s p) := by
    apply prime_coprime_test
    intro l hl hd hq
    have e := lemma56i hp hl hrs hd hq
    subst l
    have ha : (p:ℤ) ∣ (-t)^p := hprod ▸ dvd_mul_of_dvd_left hd _
    exact ht (dvd_neg.mp ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow ha))
  exact ⟨hc, combine_roots ho hc hprod⟩

lemma modp_fermat {r s t : ℤ} {p : ℕ} (hp : p.Prime) (he : r^p+s^p+t^p=0) :
    (p:ℤ) ∣ r+s+t := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hc := congrArg (fun n : ℤ => (n : ZMod p)) he
  push_cast at hc ⊢
  simpa only [ZMod.pow_card] using hc

lemma lemma56iii {r s t : ℤ} {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (hrs : IsCoprime r s)
    (he : r^p+s^p+t^p=0) (ht : (p:ℤ) ∣ t) :
    (p:ℤ) ∣ r+s ∧ (p:ℤ) ∣ quotient r s p ∧ ¬ (p:ℤ)^2 ∣ quotient r s p ∧
    ∀ (k : ℕ) (v : ℤ), 0<k → ¬ (p:ℤ) ∣ v → t=(p:ℤ)^k*v →
      ∃ w u : ℤ, ¬ (p:ℤ) ∣ w ∧ ¬ (p:ℤ) ∣ u ∧
        r+s=(p:ℤ)^(k*p-1)*w^p ∧ quotient r s p=(p:ℤ)*u^p ∧ v= -(w*u) := by
  have ho := hp.odd_of_ne_two (by omega)
  have hP := Nat.prime_iff_prime_int.mp hp
  have hd : (p:ℤ) ∣ r+s := by simpa using dvd_sub (modp_fermat hp he) ht
  have hn : ¬ (p:ℤ) ∣ r := fun h => hP.not_unit (hrs.isUnit_of_dvd' h (by
    simpa using dvd_sub hd h))
  have hm := emultiplicity_geom_sum₂_eq_one hP ho (x:=r) (y := -s) (by simpa using hd) hn
  have hval : (p:ℤ) ∣ quotient r s p ∧ ¬ (p:ℤ)^2 ∣ quotient r s p := by
    simpa [quotient] using (emultiplicity_eq_coe.mp (show
      emultiplicity (p:ℤ) (quotient r s p) = ((1:ℕ):ℕ∞) from hm))
  refine ⟨hd,hval.1,hval.2,?_⟩
  intro k v hk hv htv
  obtain ⟨B,hB⟩ := hval.1
  have hnb : ¬ (p:ℤ) ∣ B := fun h => hval.2 (by rw [hB,pow_two]; exact mul_dvd_mul_left _ h)
  let N := k*p-1
  have hN : N+1=k*p := by dsimp [N]; have := Nat.mul_pos hk hp.pos; omega
  have hprod : (r+s)*B=(p:ℤ)^N*(-v)^p := by
    apply mul_left_cancel₀ hP.ne_zero
    calc
      (p:ℤ)*((r+s)*B) = (r+s)*quotient r s p := by rw [hB]; ring
      _ = -(t^p) := by rw [factor _ _ ho]; omega
      _ = (p:ℤ)*((p:ℤ)^N*(-v)^p) := by
        rw [htv, mul_pow, ← pow_mul, ← hN, pow_succ, ho.neg_pow]; ring
  have hdN : (p:ℤ)^N ∣ r+s := ((hP.coprime_iff_not_dvd.mpr hnb).pow_left).dvd_of_dvd_mul_right
    (hprod ▸ dvd_mul_right _ _)
  obtain ⟨A,hA⟩ := hdN
  have hred : A*B=(-v)^p := by
    apply mul_left_cancel₀ (pow_ne_zero N hP.ne_zero)
    simpa only [hA, mul_assoc] using hprod
  have hc : IsCoprime A B := by
    apply prime_coprime_test
    intro l hl ha hb
    have := lemma56i hp hl hrs (hA ▸ dvd_mul_of_dvd_right ha _) (hB ▸ dvd_mul_of_dvd_right hb _)
    subst l
    exact hnb hb
  obtain ⟨w,u,hw,hu,hwuv⟩ := combine_roots ho hc hred
  refine ⟨w,u,?_,?_,by rw [hA,hw],by rw [hB,hu],hwuv⟩
  · intro h
    apply hv
    rw [hwuv]
    exact dvd_neg.mpr (dvd_mul_of_dvd_left h _)
  · intro h
    apply hv
    rw [hwuv]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right h _)

end ExpEst
