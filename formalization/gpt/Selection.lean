import Numeric

namespace ExpEstL3
open Real Finset
noncomputable section

def theta (A : Finset ℕ) : ℝ := ∑ p ∈ A, log p
def primesTo (x : ℝ) : Finset ℕ := (range (⌊x⌋₊+1)).filter Nat.Prime

private lemma mem_primesTo {x : ℝ} (hx : 0≤x) {p : ℕ} :
    p∈primesTo x ↔ (p:ℝ)≤x ∧ p.Prime := by
  simp [primesTo, Nat.le_floor_iff hx]

/-- Proposition 2.2(ii), first display, with the paper's threshold. -/
def PrimeEstimate : Prop :=
  ∀ x : ℝ, 10^15 ≤ x → |theta (primesTo x)-x| ≤ 0.00071*x

private lemma lp_nonneg (p : ℕ) : 0≤log (p:ℝ) := by
  cases p with
  | zero => simp
  | succ k => apply log_nonneg; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

lemma theta_nonneg (A : Finset ℕ) : 0≤theta A := sum_nonneg fun p _ => lp_nonneg p
private lemma theta_mono {A B : Finset ℕ} (hs : A⊆B) : theta A≤theta B :=
  sum_le_sum_of_subset_of_nonneg hs fun p _ _ => lp_nonneg p

private lemma theta_union (A B : Finset ℕ) : theta (A ∪ B) ≤ theta A + theta B := by
  have H := sum_union_inter (s₁ := A) (s₂ := B) (f := fun p : ℕ => log (p:ℝ))
  change theta (A∪B) + theta (A∩B) = theta A + theta B at H
  linarith only [H,theta_nonneg (A∩B)]

private lemma theta_many (s : Finset ℕ) (A : ℕ → Finset ℕ) :
    theta (s.biUnion A) ≤ ∑ v ∈ s, theta (A v) := by
  induction s using Finset.induction_on with
  | empty => simp [theta]
  | @insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    exact (theta_union ..).trans (add_le_add_right ih _)

/-- Proposition 2.2(ii)'s prime outside a finite set, derived from θ. -/
theorem prime_outside (pnt : PrimeEstimate) (A : Finset ℕ) :
    ∃ l : ℕ, l.Prime ∧ l∉A ∧ (l:ℝ) ≤ 1.00072*(theta A+10^15) := by
  let x := (theta A + 10^15)/(1-0.00071)
  have hx : 10^15≤x := by
    change 10^15 ≤ (theta A+10^15)/(1-0.00071)
    apply (le_div_iff₀ (by norm_num)).mpr
    linarith only [theta_nonneg A]
  have hpos : (0:ℝ)≤x := by linarith only [hx,show (0:ℝ)≤10^15 by norm_num]
  have low := (abs_le.mp (pnt x hx)).1
  have hn : ¬ primesTo x ⊆ A := by
    intro hi
    have := theta_mono hi
    change -(0.00071*x) ≤ theta (primesTo x)-x at low
    have he : (1-0.00071)*x = theta A+10^15 := by dsimp [x]; ring
    linarith only [low,this,he]
  obtain ⟨l,hl,ha⟩ := Set.not_subset.mp hn
  obtain ⟨hle,hprime⟩ := (mem_primesTo hpos).mp hl
  refine ⟨l,hprime,ha,hle.trans ?_⟩
  change (theta A+10^15)/(1-0.00071) ≤ _
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (by norm_num) (add_nonneg (theta_nonneg A) (by norm_num))

/-- Only bad places appear. n(v) is the positive integral local height,
    f(v) the residue degree. The fibre bound is the local degree formula. -/
structure LocalData where
  places : Finset ℕ
  p : ℕ → ℕ
  n : ℕ → ℕ
  f : ℕ → ℕ
  degree : ℕ
  deg_pos : 0<degree
  deg_le : (degree:ℝ)≤δ
  prime : ∀ v∈places, (p v).Prime
  npos : ∀ v∈places, 0<n v
  fpos : ∀ v∈places, 0<f v
  fibre : ∀ l, (∑ v ∈ places.filter (fun v => p v=l), f v) ≤ degree

namespace LocalData
def weight (T : LocalData) (v : ℕ) : ℝ := T.n v * (T.f v:ℝ) * log (T.p v)
def height (T : LocalData) : ℝ := (∑ v ∈ T.places, T.weight v) / T.degree
def restricted (T : LocalData) (l : ℕ) : ℝ :=
  (∑ v ∈ T.places.filter (fun v => T.p v≠l), T.weight v)/T.degree

lemma sum_weight (T : LocalData) : (∑ v ∈ T.places, T.weight v) = T.degree*T.height := by
  unfold height
  field_simp [show (T.degree:ℝ)≠0 by exact_mod_cast T.deg_pos.ne']

lemma weight_nonneg (T : LocalData) (v : ℕ) : 0≤T.weight v :=
  mul_nonneg (by positivity) (lp_nonneg _)

private lemma weight_controls (T : LocalData) {v : ℕ} (hv : v∈T.places) :
    (T.n v:ℝ)*log (T.p v) ≤ T.weight v ∧ (T.n v:ℝ)≤1.45*T.weight v := by
  have hf : (1:ℝ)≤T.f v := by exact_mod_cast T.fpos v hv
  have hn : (0:ℝ)≤T.n v := by positivity
  have hlog := log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤T.p v by exact_mod_cast (T.prime v hv).two_le)
  have hw : (T.n v:ℝ)*log (T.p v) ≤ T.weight v := by
    unfold weight
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hn hf) (lp_nonneg _)
  refine ⟨hw,?_⟩
  have h1 : 1 ≤ 1.45*log (T.p v) := by linarith only [hlog,log_two_gt_d9]
  nlinarith only [hw,mul_le_mul_of_nonneg_left h1 hn]

private lemma theta_factors (n : ℕ) (hn : 0<n) : theta n.primeFactors ≤ log (n:ℝ) := by
  have hprod := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have z : 0 < ∏ p ∈ n.primeFactors, p := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have := log_le_log (by exact_mod_cast z : (0:ℝ)<((∏ p ∈ n.primeFactors,p : ℕ):ℝ))
    (show ((∏ p ∈ n.primeFactors,p : ℕ):ℝ) ≤ (n:ℝ) by exact_mod_cast hprod)
  rw [Nat.cast_prod, log_prod (by intro p hp; exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)] at this
  exact this

private def bannedAt (T : LocalData) (s : ℝ) (v : ℕ) : Finset ℕ :=
  if s≤T.n v then (T.n v).primeFactors ∪ {T.p v} else ∅

private lemma banned_bound (T : LocalData) (H : 10^30≤T.height) {v : ℕ} (hv : v∈T.places) :
    √T.height * theta (T.bannedAt (√T.height) v) ≤
      (1+1.45*log (scale*T.height))*T.weight v := by
  have L := log_large H
  have L0 : 0≤log (scale*T.height) := (show (0:ℝ)≤82.65 by norm_num).trans L
  have h0 : 0≤T.height := by linarith only [H,show (0:ℝ)≤10^30 by norm_num]
  have ⟨hw,hn⟩ := T.weight_controls hv
  have W := T.weight_nonneg v
  unfold bannedAt
  split_ifs with big
  · have hsum := single_le_sum (fun i (_ : i ∈ T.places) => T.weight_nonneg i) hv
    rw [T.sum_weight] at hsum
    have deg := mul_le_mul_of_nonneg_right T.deg_le h0
    have hsize : (T.n v:ℝ)≤scale*T.height := by dsimp [scale]; linarith only [hn,hsum,deg]
    have hl := log_le_log (by exact_mod_cast T.npos v hv : 0<(T.n v:ℝ)) hsize
    have hs1 := theta_union (T.n v).primeFactors {T.p v}
    have hs2 : theta {T.p v} = log (T.p v) := by simp [theta]
    rw [hs2] at hs1
    have hf := theta_factors _ (T.npos v hv)
    have hs3 := mul_le_mul_of_nonneg_left (hs1.trans (add_le_add_left (hf.trans hl) _)) (sqrt_nonneg T.height)
    have hres := mul_le_mul_of_nonneg_right big (lp_nonneg (T.p v))
    have hdiv := mul_le_mul_of_nonneg_right (big.trans hn) L0
    apply hs3.trans
    rw [mul_add]
    calc
      _ ≤ (1.45*T.weight v)*log (scale*T.height) + T.weight v := add_le_add hdiv (hres.trans hw)
      _ = _ := by ring
  · simp only [theta,sum_empty,mul_zero]
    exact mul_nonneg (by linarith) W

def Eligible (T : LocalData) (l : ℕ) : Prop :=
  l.Prime ∧ √T.height ≤ l ∧ (l:ℝ) ≤ 1.464*δ*√T.height*log (scale*T.height) ∧
  (∀ v∈T.places, ¬ l ∣ T.n v) ∧ (∀ v∈T.places, T.p v=l → (T.n v:ℝ)<√T.height)

/-- (S1)–(S3) and (P1)–(P3), pp. 38–39. Including the boundary
    prime in S1 gives the same upper budget and a strict lower bound. -/
theorem select_prime (T : LocalData) (pnt : PrimeEstimate) (H : 10^30≤T.height) :
    ∃ l, T.Eligible l := by
  let s := √T.height
  let L := log (scale*T.height)
  let B := T.places.biUnion (T.bannedAt s)
  let A := primesTo s ∪ B
  have hs : 10^15≤s := sqrt_large H
  have hs0 : 0<s := by linarith only [hs,show (0:ℝ)<10^15 by norm_num]
  have hL : 82.65≤L := log_large H
  have hL0 : 0≤L := by linarith
  have hs2 : s^2=T.height := sq_sqrt (by linarith only [H,show (0:ℝ)≤10^30 by norm_num])
  have ht : s * theta B ≤ (1+1.45*L)*(T.degree*T.height) := by
    calc
      _ ≤ s * ∑ v ∈ T.places, theta (T.bannedAt s v) := mul_le_mul_of_nonneg_left (theta_many ..) hs0.le
      _ = ∑ v ∈ T.places, s*theta (T.bannedAt s v) := Finset.mul_sum ..
      _ ≤ ∑ v ∈ T.places, (1+1.45*L)*T.weight v := sum_le_sum fun v hv => T.banned_bound H hv
      _ = _ := by rw [← Finset.mul_sum, T.sum_weight]
  have hB : theta B ≤ (1+1.45*L)*δ*s := by
    apply le_of_mul_le_mul_left (a := s) _ hs0
    apply ht.trans
    rw [← hs2]
    have mult := mul_le_mul_of_nonneg_right T.deg_le (sq_nonneg s)
    nlinarith only [mul_le_mul_of_nonneg_left mult (show 0≤1+1.45*L by linarith)]
  have small := (abs_le.mp (pnt s hs)).2
  have hA : theta A ≤ 1.4621*δ*s*L := by
    have ht' := theta_union (primesTo s) B
    have hc : 2+(1+1.45*L)*δ ≤ 1.4621*δ*L := by dsimp [δ]; linarith only [hL]
    nlinarith only [ht',hB,small,hs0.le,mul_le_mul_of_nonneg_right hc hs0.le]
  obtain ⟨l,hp,hout,hl⟩ := prime_outside pnt A
  have hsmall : l∉primesTo s := fun h => hout (mem_union_left _ h)
  have hbig : l∉B := fun h => hout (mem_union_right _ h)
  have sl : s<(l:ℝ) := lt_of_not_ge (fun h => hsmall ((mem_primesTo hs0.le).mpr ⟨h,hp⟩))
  have hbudget : 10^15 ≤ 0.0001*δ*s*L := by
    have hcoef : 1≤0.0001*δ*L := by dsimp [δ]; linarith only [hL]
    nlinarith only [hs,mul_le_mul_of_nonneg_right hcoef hs0.le]
  have coeff : 1.00072*(1.4621+0.0001) ≤ (1.464:ℝ) := by norm_num
  have hi : (l:ℝ)≤1.464*δ*s*L := by
    nlinarith only [hl,hA,hbudget,mul_le_mul_of_nonneg_right coeff (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤δ) hs0.le) hL0)]
  refine ⟨l,hp,sl.le,hi,?_,?_⟩
  · intro v hv hd
    have hn : l≤T.n v := Nat.le_of_dvd (T.npos v hv) hd
    have hvbig : s≤T.n v := sl.le.trans (by exact_mod_cast hn)
    apply hbig
    exact mem_biUnion.mpr ⟨v,hv,by
      rw [bannedAt,if_pos hvbig]
      exact mem_union_left _ (hp.mem_primeFactors hd (T.npos v hv).ne')⟩
  · intro v hv hpl
    by_contra! hvbig
    apply hbig
    exact mem_biUnion.mpr ⟨v,hv,by simp [bannedAt,show s≤T.n v from hvbig,hpl]⟩

end LocalData
end
end ExpEstL3
