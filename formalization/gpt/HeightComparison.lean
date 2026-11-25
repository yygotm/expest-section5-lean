import RationalData

namespace ExpEstL2
open Real

lemma Primitive.cop_ac (T : Primitive) : IsCoprime T.a T.c := by
  have hc : T.c = -(T.b+T.a*1) := by linarith [T.sum]
  rw [hc]
  exact (T.cop.add_mul_left_right 1).neg_right

lemma Primitive.cop_bc (T : Primitive) : IsCoprime T.b T.c := by
  have hc : T.c = -(T.a+T.b*1) := by linarith [T.sum]
  rw [hc]
  exact (T.cop.symm.add_mul_left_right 1).neg_right

lemma Primitive.product_pos (T : Primitive) : 0<T.product :=
  Int.natAbs_pos.mpr (mul_ne_zero (mul_ne_zero T.ha T.hb) T.hc)

lemma Primitive.height_pos (T : Primitive) : 0<T.height :=
  (Int.natAbs_pos.mpr T.ha).trans_le (le_max_left ..)

lemma rad_pos (n : ℕ) : 0<rad n :=
  Finset.prod_pos (fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos)

lemma Primitive.radical_asQ (T : Primitive) : T.asQ.radical = rad T.product := by
  let q : ℚ := (T.a:ℚ)/T.b
  have hg := Int.isCoprime_iff_gcd_eq_one.mp T.cop.symm
  have hn : q.num = T.b.sign*T.a := by
    simp [q,← Rat.divInt_eq_div,Rat.num_divInt,hg]
  have hd : q.den = T.b.natAbs := by
    simp [q,← Rat.divInt_eq_div,Rat.den_divInt,T.hb,hg]
  have hc : -(q.num+(q.den:ℤ)) = T.b.sign*T.c := by
    rw [hn,hd,← Int.sign_mul_self]
    linear_combination -T.b.sign*T.sum
  change rad (q.num*(q.den:ℤ)* -(q.num+(q.den:ℤ))).natAbs = _
  rw [hc,hn,hd]
  simp [Primitive.product,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero T.hb,Int.natAbs_abs]

/-- Primitive representatives give unit maximum at every finite prime. -/
lemma Primitive.local_max (T : Primitive) {p : ℕ} (hp : p.Prime) :
    max (padicNorm p T.a) (max (padicNorm p T.b) (padicNorm p T.c)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hP := Nat.prime_iff_prime_int.mp hp
  apply le_antisymm (max_le (padicNorm.of_int _) (max_le (padicNorm.of_int _) (padicNorm.of_int _)))
  by_cases h : (p:ℤ)∣T.a
  · have hb := (padicNorm.int_eq_one_iff (p:=p) T.b).mpr
      (fun hb => hP.not_unit (T.cop.isUnit_of_dvd' h hb))
    exact hb ▸ (le_max_left ..).trans (le_max_right ..)
  · rw [← (padicNorm.int_eq_one_iff (p:=p) T.a).mpr h]
    exact le_max_left .. 

/-- The finite places at which the absolute values are not all equal are
    exactly the primes in the radical. -/
lemma Primitive.radical_support (T : Primitive) {p : ℕ} (hp : p.Prime) :
    p ∈ T.product.primeFactors ↔ ¬(padicNorm p T.a = padicNorm p T.b ∧
                                      padicNorm p T.b = padicNorm p T.c) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hP := Nat.prime_iff_prime_int.mp hp
  rw [Nat.mem_primeFactors, and_iff_right hp, and_iff_left T.product_pos.ne']
  change p ∣ (T.a*T.b*T.c).natAbs ↔ _
  rw [← Int.natCast_dvd,hP.dvd_mul,hP.dvd_mul]
  constructor
  · rintro h ⟨hab,hbc⟩
    have hm := T.local_max hp
    rw [hab,hbc,max_self,max_self] at hm
    have h1 := (padicNorm.int_eq_one_iff (p:=p) T.a).mp (hab.trans (hbc.trans hm))
    have h2 := (padicNorm.int_eq_one_iff (p:=p) T.b).mp (hbc.trans hm)
    have h3 := (padicNorm.int_eq_one_iff (p:=p) T.c).mp hm
    tauto
  · contrapose!
    rintro ⟨⟨ha,hb⟩,hc⟩
    simp only [(padicNorm.int_eq_one_iff _).mpr ha, (padicNorm.int_eq_one_iff _).mpr hb,
      (padicNorm.int_eq_one_iff _).mpr hc, and_self]

/-- Claim 5.3A in primitive coordinates; the finite projective term is zero. -/
lemma claim53A {x y : ℤ} (hx : x≠0) (hy : y≠0) (hc : IsCoprime x y) :
    torNon ((x:ℚ)/y) = (log x.natAbs + log y.natAbs)/2 := by
  have den_rule (a b : ℤ) (hb : b ≠ 0) (hab : IsCoprime a b) :
      ((a:ℚ)/b).den=b.natAbs := by
    rw [← Rat.divInt_eq_div,Rat.den_divInt,if_neg hb,Int.isCoprime_iff_gcd_eq_one.mp hab.symm,Nat.div_one]
  rw [torNon,inv_div,hNon,hNon,den_rule _ _ hy hc,den_rule _ _ hx hc.symm,add_comm]

noncomputable def Primitive.torSum (T : Primitive) : ℝ :=
  torNon ((T.a:ℚ)/T.c) + torNon ((T.b:ℚ)/T.c) + torNon ((T.b:ℚ)/T.a)

lemma Primitive.torSum_eq (T : Primitive) : T.torSum = log T.product := by
  rw [torSum,claim53A T.ha T.hc T.cop_ac,claim53A T.hb T.hc T.cop_bc,claim53A T.hb T.ha T.cop.symm]
  simp only [product,Int.natAbs_mul,Nat.cast_mul]
  rw [log_mul (by positivity [Int.natAbs_pos.mpr T.ha,Int.natAbs_pos.mpr T.hb]) (by exact_mod_cast Int.natAbs_ne_zero.mpr T.hc),
    log_mul (by exact_mod_cast Int.natAbs_ne_zero.mpr T.ha) (by exact_mod_cast Int.natAbs_ne_zero.mpr T.hb)]
  ring

/-- The numerator core N is coprime to the entire product abc. -/
lemma core_coprime (T : Primitive) :
    IsCoprime (T.a*T.b*T.c) (T.a^2+T.a*T.b+T.b^2) := by
  let N := T.a^2+T.a*T.b+T.b^2
  have hA : IsCoprime T.a N := by
    have h : IsCoprime T.a (T.b^2) := T.cop.pow_right
    rw [show N = T.b^2+T.a*(T.a+T.b) by dsimp [N]; ring]
    exact h.add_mul_left_right _
  have hB : IsCoprime T.b N := by
    have h : IsCoprime T.b (T.a^2) := T.cop.symm.pow_right
    rw [show N = T.a^2+T.b*(T.a+T.b) by dsimp [N]; ring]
    exact h.add_mul_left_right _
  have hC : IsCoprime T.c N := by
    have h : IsCoprime T.c (T.a^2) := T.cop_ac.symm.pow_right
    have he : N=T.a^2+T.c*(-T.b) := by dsimp [N]; linear_combination T.b*T.sum
    rw [he]
    exact h.add_mul_left_right _
  exact (hA.mul_left hB).mul_left hC

/-- No odd prime factor can cancel in the displayed formula for j.
    More precisely (abc)² divides 2⁸ times the reduced denominator of j. -/
lemma denom_divisibility (T : Primitive) : T.product^2 ∣ 256*T.asQ.curve.j.den := by
  let J := T.asQ.curve.j
  let P := T.a*T.b*T.c
  let N := T.a^2+T.a*T.b+T.b^2
  have hj : (J.num:ℚ)/J.den = (256:ℚ)*(N:ℚ)^3/(P:ℚ)^2 := by
    rw [Rat.num_div_den]
    simpa [J,P,N,Primitive.asQ] using T.asQ.j_formula
  have hp : P≠0 := mul_ne_zero (mul_ne_zero T.ha T.hb) T.hc
  have cross : J.num*P^2=256*N^3*(J.den:ℤ) := by
    exact_mod_cast (div_eq_div_iff (by exact_mod_cast J.den_ne_zero)
      (pow_ne_zero 2 (by exact_mod_cast hp))).mp hj
  have hc : IsCoprime (P^2) (N^3) := (core_coprime T).pow_left.pow_right
  have hd : P^2 ∣ (256*(J.den:ℤ))*N^3 := ⟨J.num,by linear_combination -cross⟩
  have d := hc.dvd_of_dvd_mul_right hd
  simpa [Primitive.product,P,Int.natAbs_mul,Int.natAbs_pow,J] using (Int.natAbs_dvd_natAbs.mpr d)

lemma product_log_bound (T : Primitive) :
    log T.product ≤ hNon T.asQ.curve.j/2 + 4*log 2 := by
  let J := T.asQ.curve.j
  have d := Nat.le_of_dvd (show 0<256*J.den by exact Nat.mul_pos (by decide) J.den_pos) (denom_divisibility T)
  have hr : (T.product:ℝ)^2 ≤ 256*(J.den:ℝ) := by exact_mod_cast d
  have h := log_le_log (pow_pos (by exact_mod_cast T.product_pos) _) hr
  rw [log_pow, log_mul (by norm_num) (by exact_mod_cast J.den_ne_zero),
    show (256:ℝ)=2^8 by norm_num,log_pow] at h
  change log T.product ≤ log J.den/2+4*log 2
  norm_num1 at h
  linarith

/-- The first inequality (*1) in the proof of Claim 5.3C, equivalently (†1) of 5.4. -/
lemma toric_comparison (T : Primitive) :
    T.torSum/3 ≤ hNon T.asQ.curve.j/6 + 4/3*log 2 := by
  rw [T.torSum_eq]
  linarith [product_log_bound T]


/-- Claim 5.3B before division by the nonzero largest coordinate. -/
lemma claim53B {x y z : ℤ} (hs : x+y+z=0) (hxy : x.natAbs≤y.natAbs) :
    z.natAbs ≤ 2*y.natAbs := by
  have h := Int.natAbs_add_le x y
  rw [show x+y = -z by omega,Int.natAbs_neg] at h
  omega

private lemma coordinate_sq {x y z : ℤ} (hx : x≠0) (hy : y≠0) (hs : x+y+z=0) :
    z.natAbs^2 ≤ 2*(x.natAbs*y.natAbs*z.natAbs) := by
  have hX := Int.natAbs_pos.mpr hx
  have hY := Int.natAbs_pos.mpr hy
  have h : z.natAbs ≤ 2*(x.natAbs*y.natAbs) := by
    rcases le_total x.natAbs y.natAbs with h | h
    · have h' : y.natAbs≤x.natAbs*y.natAbs := Nat.le_mul_of_pos_left _ hX
      have := claim53B hs h
      omega
    · have h' : x.natAbs≤x.natAbs*y.natAbs := Nat.le_mul_of_pos_right _ hY
      have := claim53B (x:=y) (y:=x) (z:=z) (by omega) h
      omega
  calc
    z.natAbs^2 = z.natAbs*z.natAbs := sq _
    _ ≤ (2*(x.natAbs*y.natAbs))*z.natAbs := Nat.mul_le_mul_right _ h
    _ = _ := by ring

lemma Primitive.height_sq_le (T : Primitive) : T.height^2≤2*T.product := by
  unfold height product
  simp only [Int.natAbs_mul]
  rcases max_choice T.a.natAbs (max T.b.natAbs T.c.natAbs) with ha|ha
  · rw [ha]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using
      coordinate_sq T.hb T.hc (z:=T.a) (by linarith [T.sum])
  rw [ha]
  rcases max_choice T.b.natAbs T.c.natAbs with hb|hc
  · rw [hb]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using
      coordinate_sq T.ha T.hc (z:=T.b) (by linarith [T.sum])
  · rw [hc]
    exact coordinate_sq T.ha T.hb T.sum

/-- Claim 5.3C, with the logarithmic constants as printed. -/
lemma claim53C (D : QTriple) :
    2/3 * log D.height - 5/3 * log 2 ≤ hNon D.curve.j/6 := by
  let T := D.primitive
  have hs : (T.height:ℝ)^2 ≤ 2*(T.product:ℝ) := by exact_mod_cast T.height_sq_le
  have hh := log_le_log (pow_pos (by exact_mod_cast T.height_pos) _) hs
  rw [log_pow,log_mul (by norm_num) (by exact_mod_cast T.product_pos.ne')] at hh
  norm_num1 at hh
  have ht := toric_comparison T
  rw [T.torSum_eq] at ht
  rw [D.j_primitive]
  change 2/3 * log T.height - 5/3*log 2 ≤ hNon T.asQ.curve.j/6
  linarith

end ExpEstL2

