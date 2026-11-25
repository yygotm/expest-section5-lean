import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ExpEst
open Real

def primeRad (n : ℕ) : ℕ := ∏ l ∈ n.primeFactors, l

noncomputable def hOne : ℝ := 3.4 * 10^30
noncomputable def heightFactor : ℝ := (2:ℝ) ^ (5/2 : ℝ)

/-- For q = a/b write the primitive triple as (q.num, q.den, -q.num-q.den).
    The three arguments below are the absolute values of its coordinates. -/
noncomputable def estimateAt (A B C : ℕ) : Prop :=
  let R := ((primeRad (A*B*C) : ℝ)^3)
  let E := Real.exp (hOne/4)
  ((max A (max B C) : ℕ) : ℝ) ≤ heightFactor * max E R ∧
    heightFactor * max E R ≤ heightFactor * E * R

/-- Theorem 5.3(ii) with L = ℚ and ε = 1; both displayed inequalities. -/
def Theorem53iiQ : Prop :=
  ∀ a b c : ℚ, a≠0 → b≠0 → c≠0 → a+b+c=0 →
    let q := a/b
    estimateAt q.num.natAbs q.den (q.num + (q.den:ℤ)).natAbs

lemma primitive_bound (h : Theorem53iiQ) {A B : ℕ} (ha : 0<A) (hb : 0<B)
    (hc : A.Coprime B) :
    ((A+B:ℕ):ℝ) ≤ heightFactor * exp (hOne/4) * (primeRad (A*B*(A+B)) : ℝ)^3 := by
  let q : ℚ := (A:ℚ)/B
  have hz : 0 < (B:ℤ) := by exact_mod_cast hb
  have hcop : (A:ℤ).natAbs.Coprime (B:ℤ).natAbs := by simpa using hc
  have hnum : q.num=(A:ℤ) := by simpa [q] using Rat.num_div_eq_of_coprime hz hcop
  have hden : q.den=B := by exact_mod_cast (show (q.den:ℤ)=(B:ℤ) by
    simpa [q] using Rat.den_div_eq_of_coprime hz hcop)
  have H := h A B (-(A+B)) (by positivity) (by positivity) (neg_ne_zero.mpr (by positivity : (A:ℚ)+B ≠ 0)) (by ring)
  change estimateAt q.num.natAbs q.den (q.num+(q.den:ℤ)).natAbs at H
  rw [hnum,hden,Int.natAbs_natCast,← Nat.cast_add,Int.natAbs_natCast] at H
  have out := H.1.trans H.2
  simpa only [max_eq_right (show B≤A+B by omega), max_eq_right (show A≤A+B by omega)] using out

/-- A nonzero rational input satisfying both inequalities, without assuming 5.3. -/
lemma example_one_one : estimateAt 1 1 2 := by
  have hr : primeRad (1*1*2)=2 := by simp [primeRad, Nat.prime_two.primeFactors]
  have hE : 1 ≤ exp (hOne/4) := Real.one_le_exp (by norm_num [hOne])
  have hK : 1 ≤ heightFactor := Real.one_le_rpow (by norm_num) (by norm_num)
  unfold estimateAt
  rw [hr]
  change (2:ℝ) ≤ heightFactor * max (exp (hOne/4)) (2^3) ∧
    heightFactor * max (exp (hOne/4)) (2^3) ≤ heightFactor * exp (hOne/4) * 2^3
  constructor
  · calc
      (2:ℝ) ≤ 1*2^3 := by norm_num
      _ ≤ heightFactor * max (exp (hOne/4)) (2^3) :=
        mul_le_mul hK (le_max_right ..) (by norm_num) (by linarith)
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤heightFactor)
    apply max_le
    · exact le_mul_of_one_le_right (by positivity) (by norm_num)
    · exact le_mul_of_one_le_left (by norm_num) hE

noncomputable def fermatLeft (P : ℝ) : ℝ := (P-9)*(-1+P*logb 2 (P+1))
noncomputable def fermatRight : ℝ := 5/2+logb 2 (exp 1)*hOne/4

lemma paper_upper_numeric : fermatRight < 1.227 * 10^30 := by
  unfold fermatRight hOne logb
  rw [log_exp]
  have h2 := log_two_gt_d9
  have hi : 1/log 2 < (1.443:ℝ) := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  linarith

/-- Certify the paper's intermediate bound with 1.44, already at the endpoint. -/
lemma paper_lower_numeric {P : ℝ} (hP : 161500000000000 ≤ P) :
    1.227 * 10^30 < (P-9)*(-1+1.44*P*log (P+1)) ∧
    (P-9)*(-1+1.44*P*log (P+1)) < fermatLeft P := by
  have hpos : 0<P := by linarith
  have cert : (2:ℝ)^755 < (161500000000000:ℝ)^16 := by
    set_option exponentiation.threshold 1024 in norm_num
  have hlarge := cert.trans_le (pow_le_pow_left₀ (by norm_num) (by linarith : 161500000000000 ≤ P+1) 16)
  have hlog := Real.log_lt_log (by positivity) hlarge
  rw [log_pow,log_pow] at hlog
  norm_num1 at hlog
  have hL : 32.69 < log (P+1) := by linarith [log_two_gt_d9]
  have hprod := mul_le_mul hP hL.le (by norm_num) hpos.le
  constructor
  · calc
      (1.227:ℝ)*10^30 < (161500000000000-9)*(-1+1.44*161500000000000*32.69) := by norm_num
      _ ≤ _ := mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  · have hi : (1.44:ℝ)<1/log 2 := (lt_div_iff₀ (by linarith [log_two_gt_d9])).mpr (by linarith [log_two_lt_d9])
    have hi' := mul_lt_mul_of_pos_right hi (mul_pos hpos (by linarith : 0<log (P+1)))
    unfold fermatLeft logb
    apply mul_lt_mul_of_pos_left _ (by linarith)
    simp only [div_eq_mul_inv, one_mul] at hi' ⊢
    linarith only [hi']

/-- A common scalar takes the displayed primitive representative back to (a,b,c). -/
lemma primitive_representative {a b c : ℚ} (hb : b ≠ 0) (he : a+b+c=0) :
    let q := a/b
    ∃ scale : ℚ, scale ≠ 0 ∧ a = scale * q.num ∧ b = scale * q.den ∧
      c = scale * (-(q.num + (q.den:ℤ)) : ℤ) := by
  let q := a/b
  have hd : (q.den:ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.num:ℚ)/q.den = a/b := Rat.num_div_den q
  have hr := (div_eq_div_iff hd hb).mp hq
  have ha : a=(b/q.den)*q.num := by
    rw [div_mul_eq_mul_div,eq_div_iff hd]; linarith
  have hB : b=(b/q.den)*q.den := (div_mul_cancel₀ b hd).symm
  refine ⟨b/q.den,div_ne_zero hb hd,ha,hB,?_⟩
  push_cast
  linarith only [he,ha,hB]

/-- On a primitive triple a finite place enters the radical exactly when
    the three finite valuations are not all equal. -/
lemma finite_support_iff {A B C l : ℕ} (hl : l.Prime) (ha : A≠0) (hb : B≠0)
    (hc : C≠0) (cop : A.Coprime B) :
    l ∈ (A*B*C).primeFactors ↔
      ¬ (A.factorization l = B.factorization l ∧ B.factorization l = C.factorization l) := by
  have hn : A*B*C≠0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hmin : A.factorization l=0 ∨ B.factorization l=0 := by
    by_cases hd : l∣A
    · exact Or.inr (Nat.factorization_eq_zero_of_not_dvd
        (fun hb' => Nat.not_coprime_of_dvd_of_dvd hl.one_lt hd hb' cop))
    · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hd)
  rw [Nat.mem_primeFactors, hl.dvd_mul, hl.dvd_mul]
  constructor
  · rintro ⟨_,hd,_⟩ ⟨h₁,h₂⟩
    have za : A.factorization l=0 := hmin.elim id (h₁.trans ·)
    rcases hd with (hd | hd) | hd
    · have := hl.factorization_pos_of_dvd ha hd; omega
    · have := hl.factorization_pos_of_dvd hb hd; omega
    · have := hl.factorization_pos_of_dvd hc hd; omega
  · intro h
    refine ⟨hl,?_,hn⟩
    by_contra! H
    exact h ⟨(Nat.factorization_eq_zero_of_not_dvd H.1.1).trans
        (Nat.factorization_eq_zero_of_not_dvd H.1.2).symm,
      (Nat.factorization_eq_zero_of_not_dvd H.1.2).trans (Nat.factorization_eq_zero_of_not_dvd H.2).symm⟩

/-- Any triple up to this height satisfies the full bound unconditionally.
    Thus a putative counterexample has to lie strictly above this threshold. -/
lemma estimateAt_of_height_le {A B C : ℕ}
    (h : ((max A (max B C):ℕ):ℝ) ≤ heightFactor*exp (hOne/4)) : estimateAt A B C := by
  have hK : 0 ≤ heightFactor := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
  have hE : 1 ≤ exp (hOne/4) := Real.one_le_exp (by norm_num [hOne])
  have hr : 0 < primeRad (A*B*C) := Finset.prod_pos (fun _ hl => (Nat.prime_of_mem_primeFactors hl).pos)
  have hr' : (1:ℝ) ≤ (primeRad (A*B*C):ℝ)^3 := one_le_pow₀ (by exact_mod_cast hr)
  refine ⟨h.trans (mul_le_mul_of_nonneg_left (le_max_left ..) hK),?_⟩
  rw [mul_assoc heightFactor]
  apply mul_le_mul_of_nonneg_left _ hK
  exact max_le (le_mul_of_one_le_right (exp_pos _).le hr') (le_mul_of_one_le_left (by positivity) hE)

end ExpEst
