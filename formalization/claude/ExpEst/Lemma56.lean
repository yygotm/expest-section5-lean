import ExpEst.Lemma55

/-!
# ExpEst Lemma 5.6

Setting of the paper: `p ≥ 3` prime; `r, s, t` nonzero coprime integers with
`r^p + s^p + t^p = 0`.  We record only the hypotheses each part uses:
(i) needs `IsCoprime r s`; (ii), (iii) also need the Fermat relation.
(Under the relation, `gcd(r, s, t) = 1` and `IsCoprime r s` are equivalent.)
-/

namespace ExpEst

open Finset

variable {p : ℕ}

/-- `(r + s) * Q = (-t)^p` from the Fermat relation. -/
theorem add_mul_Q_eq_neg_pow (hodd : Odd p) {r s t : ℤ} (h : r ^ p + s ^ p + t ^ p = 0) :
    (r + s) * Q p r s = (-t) ^ p := by
  rw [add_mul_Q hodd, Odd.neg_pow hodd]
  linarith

/-- Lemma 5.6 (i): a prime dividing both `r + s` and `Q p r s` is `p`. -/
theorem lemma56_i (hp : p.Prime) (hodd : Odd p) {r s : ℤ} (hrs : IsCoprime r s)
    {l : ℕ} (hl : l.Prime) (h1 : (l : ℤ) ∣ r + s) (h2 : (l : ℤ) ∣ Q p r s) : l = p := by
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h3 : (l : ℤ) ∣ p * s ^ (p - 1) := by
    have := dvd_sub h2 (h1.trans (lemma55 hodd r s))
    simpa using this
  rcases hlZ.dvd_or_dvd h3 with h4 | h4
  · exact (Nat.prime_dvd_prime_iff_eq hl hp).mp (Int.natCast_dvd_natCast.mp h4)
  · have hls : (l : ℤ) ∣ s := hlZ.dvd_of_dvd_pow h4
    have hlr : (l : ℤ) ∣ r := by
      have := dvd_sub h1 hls
      simpa using this
    exact absurd (hrs.isUnit_of_dvd' hlr hls) hlZ.not_unit

/-- Two integers are coprime if every prime dividing both is `p` and `p` does not divide
the second one. -/
theorem isCoprime_of_prime_dvd {a b : ℤ}
    (H : ∀ l : ℕ, l.Prime → (l : ℤ) ∣ a → (l : ℤ) ∣ b → l = p) (hpb : ¬ (p : ℤ) ∣ b) :
    IsCoprime a b := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  apply Nat.coprime_of_dvd
  intro k hk h1 h2
  have h1' : (k : ℤ) ∣ a := Int.natCast_dvd.mpr h1
  have h2' : (k : ℤ) ∣ b := Int.natCast_dvd.mpr h2
  have := H k hk h1' h2'
  subst this
  exact hpb h2'

/-- Lemma 5.6 (ii): if `p ∤ t`, then `r + s` and `Q` are coprime, and
`r + s = u^p`, `Q = ũ^p`, `t = -u ũ`. -/
theorem lemma56_ii (hp : p.Prime) (hodd : Odd p) {r s t : ℤ} (hrs : IsCoprime r s)
    (h : r ^ p + s ^ p + t ^ p = 0) (hpt : ¬ (p : ℤ) ∣ t) :
    IsCoprime (r + s) (Q p r s) ∧
      ∃ u u' : ℤ, r + s = u ^ p ∧ Q p r s = u' ^ p ∧ t = -(u * u') := by
  have e := add_mul_Q_eq_neg_pow hodd h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (r + s) (Q p r s) := by
    apply isCoprime_of_prime_dvd (p := p) (fun l hl h1 h2 => lemma56_i hp hodd hrs hl h1 h2)
    intro hQ
    apply hpt
    have : (p : ℤ) ∣ (-t) ^ p := e ▸ dvd_mul_of_dvd_right hQ _
    exact dvd_neg.mp (hpZ.dvd_of_dvd_pow this)
  refine ⟨hcop, ?_⟩
  obtain ⟨⟨u, hu⟩, ⟨u', hu'⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hcop hodd e
  refine ⟨u, u', hu, hu', ?_⟩
  have : (u * u') ^ p = (-t) ^ p := by rw [mul_pow, ← hu, ← hu', e]
  have := (Odd.pow_inj hodd).mp this
  linarith

/-- Lemma 5.6 (iii), first part: if `p ∣ t`, then `p ∣ r + s`, `p ∣ Q`, `p² ∤ Q`. -/
theorem lemma56_iii (hp : p.Prime) (hodd : Odd p) {r s t : ℤ} (hrs : IsCoprime r s)
    (ht : t ≠ 0) (h : r ^ p + s ^ p + t ^ p = 0) (hpt : (p : ℤ) ∣ t) :
    (p : ℤ) ∣ r + s ∧ (p : ℤ) ∣ Q p r s ∧ ¬ (p : ℤ) ^ 2 ∣ Q p r s := by
  haveI := Fact.mk hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have e := add_mul_Q_eq_neg_pow hodd h
  -- (r + s)^p ≡ r^p + s^p ≡ -t^p ≡ 0 (mod p)
  have hprs : (p : ℤ) ∣ r + s := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have ht0 : ((t : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mpr hpt
    have hh : ((r ^ p + s ^ p + t ^ p : ℤ) : ZMod p) = 0 := by rw [h]; simp
    push_cast at hh ⊢
    simp only [ZMod.pow_card] at hh
    simpa [ht0] using hh
  have hpQ : (p : ℤ) ∣ Q p r s := by
    have := dvd_add (hprs.trans (lemma55 hodd r s)) (dvd_mul_right (p : ℤ) (s ^ (p - 1)))
    simpa using this
  refine ⟨hprs, hpQ, ?_⟩
  -- p ∤ r (otherwise p ∣ s)
  have hnr : ¬ (p : ℤ) ∣ r := by
    intro hr'
    have hs' : (p : ℤ) ∣ s := by
      have := dvd_sub hprs hr'
      simpa using this
    exact hpZ.not_unit (hrs.isUnit_of_dvd' hr' hs')
  have hrs0 : r + s ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e
    exact ht (neg_eq_zero.mp (pow_eq_zero_iff hodd.pos.ne' |>.mp e.symm))
  -- lifting the exponent: v_p(r^p + s^p) = v_p(r + s) + 1
  have hlte := Int.emultiplicity_pow_add_pow hp hodd hprs hnr hodd
  rw [← add_mul_Q hodd, emultiplicity_mul hpZ, hp.emultiplicity_self] at hlte
  have hfin : FiniteMultiplicity (p : ℤ) (r + s) :=
    Int.finiteMultiplicity_iff.mpr ⟨by simp [hp.one_lt.ne'], hrs0⟩
  rw [hfin.emultiplicity_eq_multiplicity] at hlte
  have hQ1 : emultiplicity (p : ℤ) (Q p r s) = 1 := by
    have := (WithTop.add_left_inj (WithTop.coe_ne_top (a := multiplicity (p : ℤ) (r + s)))).mp hlte
    exact this
  intro h2
  have := (pow_dvd_iff_le_emultiplicity).mp h2
  rw [hQ1] at this
  norm_num at this

/-- Lemma 5.6 (iii), second part: writing `t = p^k v` (`k > 0`, `p ∤ v`), there are
`w, w̃` prime to `p` with `r + s = p^(kp-1) w^p`, `Q = p w̃^p`, `v = -w w̃`. -/
theorem lemma56_iii' (hp : p.Prime) (hodd : Odd p) {r s t : ℤ} (hrs : IsCoprime r s)
    (ht : t ≠ 0) (h : r ^ p + s ^ p + t ^ p = 0) {k : ℕ} {v : ℤ} (hk : 0 < k)
    (hpv : ¬ (p : ℤ) ∣ v) (htv : t = (p : ℤ) ^ k * v) :
    ∃ w w' : ℤ, ¬ (p : ℤ) ∣ w ∧ ¬ (p : ℤ) ∣ w' ∧
      r + s = (p : ℤ) ^ (k * p - 1) * w ^ p ∧ Q p r s = p * w' ^ p ∧ v = -(w * w') := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpt : (p : ℤ) ∣ t := htv ▸ dvd_mul_of_dvd_left (dvd_pow_self _ hk.ne') v
  obtain ⟨_, hpQ, hp2Q⟩ := lemma56_iii hp hodd hrs ht h hpt
  obtain ⟨Q', hQ'⟩ := hpQ
  have hpQ' : ¬ (p : ℤ) ∣ Q' := by
    rintro ⟨m, hm⟩
    exact hp2Q ⟨m, by rw [hQ', hm]; ring⟩
  have e := add_mul_Q_eq_neg_pow hodd h
  have hkp : 1 ≤ k * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hk.ne' hp.ne_zero)
  -- (r + s) Q' = p^(kp-1) (-v)^p
  have e2 : (r + s) * Q' = (p : ℤ) ^ (k * p - 1) * (-v) ^ p := by
    apply mul_left_cancel₀ hp0
    have : (p : ℤ) * (p : ℤ) ^ (k * p - 1) = (p : ℤ) ^ (k * p) := by
      rw [← pow_succ']
      congr 1
      omega
    calc (p : ℤ) * ((r + s) * Q') = (r + s) * Q p r s := by rw [hQ']; ring
      _ = (-t) ^ p := e
      _ = (p : ℤ) * ((p : ℤ) ^ (k * p - 1) * (-v) ^ p) := by
        rw [htv, ← mul_assoc, this, Odd.neg_pow hodd, Odd.neg_pow hodd, mul_pow, ← pow_mul]
        ring
  -- p^(kp-1) ∣ r + s
  have hcopp : IsCoprime ((p : ℤ) ^ (k * p - 1)) Q' :=
    ((Prime.coprime_iff_not_dvd hpZ).mpr hpQ').pow_left
  have hdvd : (p : ℤ) ^ (k * p - 1) ∣ r + s :=
    hcopp.dvd_of_dvd_mul_right ⟨(-v) ^ p, e2⟩
  obtain ⟨R, hR⟩ := hdvd
  have hpk0 : (p : ℤ) ^ (k * p - 1) ≠ 0 := pow_ne_zero _ hp0
  have e3 : R * Q' = (-v) ^ p := by
    apply mul_left_cancel₀ hpk0
    rw [← mul_assoc, ← hR, e2]
  -- R and Q' are coprime
  have hcop : IsCoprime R Q' := by
    apply isCoprime_of_prime_dvd (p := p) _ hpQ'
    intro l hl h1 h2
    apply lemma56_i hp hodd hrs hl
    · rw [hR]; exact dvd_mul_of_dvd_right h1 _
    · rw [hQ']; exact dvd_mul_of_dvd_right h2 _
  obtain ⟨⟨w, hw⟩, ⟨w', hw'⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hcop hodd e3
  have hv : v = -(w * w') := by
    have : (w * w') ^ p = (-v) ^ p := by rw [mul_pow, ← hw, ← hw', e3]
    have := (Odd.pow_inj hodd).mp this
    linarith
  refine ⟨w, w', ?_, ?_, ?_, ?_, hv⟩
  · intro hw0
    exact hpv (hv ▸ (dvd_neg.mpr (dvd_mul_of_dvd_left hw0 _)))
  · intro hw0
    exact hpQ' (hw' ▸ dvd_pow hw0 hp.ne_zero)
  · rw [hR, hw]
  · rw [hQ', hw']

end ExpEst
