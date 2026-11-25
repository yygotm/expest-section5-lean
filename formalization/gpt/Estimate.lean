import Arithmetic
import Mathlib.NumberTheory.FLT.Basic

namespace ExpEst

private lemma small_multiple {P d : ℤ} (h : P ∣ d) (hl : -P < d) (hu : d < P) : d=0 := by
  by_cases hn : 0 ≤ d
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hn hu h
  · have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ -d) (by omega : -d < P) (dvd_neg.mpr h)
    omega

private lemma modp_pow {p : ℕ} (hp : p.Prime) (x : ℤ) :
    (x^p : ℤ) ≡ x [ZMOD (p:ℤ)] := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  push_cast
  exact ZMod.pow_card _

private lemma root_factor {p : ℕ} {r s t : ℤ} (hp : p.Prime) (h3 : 3≤p)
    (hc : IsCoprime r s) (he : r^p+s^p=t^p) (hs : 0<r+s) (ht : ¬(p:ℤ)∣t) :
    ∃ a : ℤ, 0<a ∧ r+s=a^p ∧ a∣t := by
  have ho := hp.odd_of_ne_two (by omega)
  obtain ⟨_,a,b,ha,_,hab⟩ := lemma56ii hp h3 hc (t := -t)
    (by rw [ho.neg_pow,he]; ring) (by simpa using ht)
  refine ⟨a,ho.pow_pos_iff.mp (ha ▸ hs),ha,b,by omega⟩

private lemma two_even_impossible {p : ℕ} (ho : Odd p) (h3 : 3≤p) {u A B T : ℤ}
    (hu : 0<u) (hAB : u=A-B) (heu : (2:ℤ)∣u) (hA : ¬(2:ℤ)∣A)
    (hd : u∣T) (he : A^p-B^p=2*T-u^p) : False := by
  obtain ⟨m,hm⟩ := hd
  let Q := ∑ i ∈ Finset.range p, A^i*B^(p-1-i)
  have hg : Q*u=A^p-B^p := hAB ▸ geom_sum₂_mul A B p
  have hq : Q=2*m-u^(p-1) := by
    apply mul_right_cancel₀ hu.ne'
    rw [hg, he, hm, sub_mul, ← pow_succ, show p-1+1=p by omega]
    ring
  have hdQ : (2:ℤ)∣Q := by
    rw [hq]
    exact dvd_sub (dvd_mul_right _ _) (dvd_pow heu (by omega))
  have hh := (dvd_geom_sum₂_iff_of_dvd_sub' (n:=p) (x:=A) (y:=B) (hAB ▸ heu)).mp hdQ
  have prime2 : Prime (2:ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
  rcases prime2.dvd_or_dvd hh with h | h
  · have h' : 2 ∣ p := by exact_mod_cast h
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h')
  · exact hA (prime2.dvd_of_dvd_pow h)

private lemma pair_zx {p : ℕ} {x y z : ℤ} (hp : p.Prime) (h3 : 3≤p)
    (hc : IsCoprime x y) (hz : 0<z) (he : x^p+y^p=z^p) : IsCoprime z (-x) := by
  have ho := hp.odd_of_ne_two (by omega)
  apply isCoprime_of_prime_dvd (by rintro ⟨h,_⟩; omega)
  intro l hl hz' hx'
  have hy := dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT hl hz' hx'
    (c := -y) (n:=p) (by rw [ho.neg_pow,ho.neg_pow]; linarith)
  exact hl.not_unit (hc.isUnit_of_dvd' (dvd_neg.mp hx') (dvd_neg.mp hy))

private lemma divides_x_case {p : ℕ} {x y z : ℤ} (hp : p.Prime) (h3 : 3≤p)
    (hx : 0<x) (hy : 0<y) (hc : IsCoprime x y) (he : x^p+y^p=z^p)
    (hxz : x<z) (hyz : y<z) (htri : z≤x+y) (hdx : (p:ℤ)∣x) :
    ((p:ℤ)+1)^p<2*z := by
  have ho := hp.odd_of_ne_two (by omega)
  have hP := Nat.prime_iff_prime_int.mp hp
  have hny : ¬(p:ℤ)∣y := fun h => hP.not_unit (hc.isUnit_of_dvd' hdx h)
  have hzx := pair_zx hp h3 hc (by omega) he
  have hnz : ¬(p:ℤ)∣z := fun h => hP.not_unit (hzx.isUnit_of_dvd' h (dvd_neg.mpr hdx))
  obtain ⟨a,ha,hap,_⟩ := root_factor hp h3 hc he (by omega) hnz
  obtain ⟨b,hb,hbp,_⟩ := root_factor hp h3 hzx (by rw [ho.neg_pow]; linarith) (by omega) hny
  have hzmod := modp_fermat hp (r:=x) (s:=y) (t := -z) (by rw [ho.neg_pow,he]; ring)
  have hba : (p:ℤ)∣b-a := by
    have h := (modp_pow hp b).sub (modp_pow hp a)
    rw [← hbp, ← hap] at h
    apply Int.modEq_zero_iff_dvd.mp
    apply h.symm.trans
    apply Int.modEq_zero_iff_dvd.mpr
    rw [show z + -x - (x+y) = -(x+y+ -z) - x by ring]
    exact dvd_sub (dvd_neg.mpr hzmod) hdx
  by_contra! hn
  have haa : a≤(p:ℤ) := by
    by_contra! hf
    have h := ho.strictMono_pow.monotone (show (p:ℤ)+1≤a by omega)
    omega
  have hbb : b≤(p:ℤ) := by
    by_contra! hf
    have h := ho.strictMono_pow.monotone (show (p:ℤ)+1≤b by omega)
    omega
  have hbma := small_multiple hba (by omega) (by omega)
  have hab : a=b := by omega
  rw [← hab] at hbp
  omega

private lemma prime_to_xyz {p : ℕ} {x y z : ℤ} (hp : p.Prime) (h3 : 3≤p)
    (hx : 0<x) (hy : 0<y) (hc : IsCoprime x y) (he : x^p+y^p=z^p)
    (hxz : x<z) (hyz : y<z) (htri : z≤x+y)
    (hnx : ¬(p:ℤ)∣x) (hny : ¬(p:ℤ)∣y) (hnz : ¬(p:ℤ)∣z) :
    ((p:ℤ)+1)^p<2*z := by
  have ho := hp.odd_of_ne_two (by omega)
  obtain ⟨a,ha,hap,haz⟩ := root_factor hp h3 hc he (by omega) hnz
  have hzx := pair_zx hp h3 hc (by omega) he
  have hzy := pair_zx (z:=z) hp h3 hc.symm (by omega) (by rwa [add_comm])
  obtain ⟨b,hb,hbp,hby⟩ := root_factor hp h3 hzx (by rw [ho.neg_pow]; linarith) (by omega) hny
  obtain ⟨c,hc',hcp,hcx⟩ := root_factor hp h3 hzy (by rw [ho.neg_pow]; linarith) (by omega) hnx
  by_contra! hn
  have haa : a≤(p:ℤ) := by
    by_contra! hf
    have h := ho.strictMono_pow.monotone (show (p:ℤ)+1≤a by omega)
    omega
  have hba : b<a := ho.strictMono_pow.lt_iff_lt.mp (by omega)
  have hca : c<a := ho.strictMono_pow.lt_iff_lt.mp (by omega)
  have hzmod := modp_fermat hp (r:=x) (s:=y) (t := -z) (by rw [ho.neg_pow,he]; ring)
  have hmod := ((modp_pow hp b).add (modp_pow hp c)).sub (modp_pow hp a)
  rw [← hbp, ← hcp, ← hap] at hmod
  have hd : (p:ℤ) ∣ b+c-a := by
    apply Int.modEq_zero_iff_dvd.mp (hmod.symm.trans (Int.modEq_zero_iff_dvd.mpr ?_))
    rw [show z + -x + (z + -y) - (x+y) = (-2)*(x+y+ -z) by ring]
    exact dvd_mul_of_dvd_right hzmod (-2)
  have habc := small_multiple hd (by omega) (by omega)
  have notboth (heb : (2:ℤ)∣b) (hec : (2:ℤ)∣c) : False :=
    (show Prime (2:ℤ) from Nat.prime_iff_prime_int.mp Nat.prime_two).not_unit (hc.isUnit_of_dvd' (hec.trans hcx) (heb.trans hby))
  by_cases heb : (2:ℤ)∣b
  · exact two_even_impossible ho h3 hb (A:=a) (B:=c) (by omega) heb
      (fun h => notboth heb (by omega)) hby (by omega)
  by_cases hec : (2:ℤ)∣c
  · exact two_even_impossible ho h3 hc' (A:=a) (B:=b) (by omega) hec
      (fun h => heb (by omega)) hcx (by omega)
  exact two_even_impossible ho h3 ha (A:=b) (B := -c) (by omega) (by omega) heb haz
    (by rw [ho.neg_pow]; omega)

private lemma threshold_power {p : ℕ} (h3 : 3≤p) :
    ((p:ℤ)+1)^p ≤ (p:ℤ)^(2*p-1) := by
  have aux (n : ℕ) : (2:ℤ)^(n+3) ≤ 3^(n+2) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n+1+3=n+3+1 by omega, show n+1+2=n+2+1 by omega, pow_succ, pow_succ (3:ℤ)]
      linarith [show 0≤(3:ℤ)^(n+2) by positivity]
  have ha := aux (p-3)
  rw [show p-3+3=p by omega, show p-3+2=p-1 by omega] at ha
  calc
    ((p:ℤ)+1)^p ≤ (2*(p:ℤ))^p := pow_le_pow_left₀ (by positivity) (by omega) _
    _ = (2:ℤ)^p*(p:ℤ)^p := mul_pow _ _ _
    _ ≤ (p:ℤ)^(p-1)*(p:ℤ)^p := by
      exact mul_le_mul_of_nonneg_right (ha.trans (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast h3) _)) (by positivity)
    _ = _ := by rw [← pow_add, show p-1+p=2*p-1 by omega]

private lemma divides_z_case {p : ℕ} {x y z : ℤ} (hp : p.Prime) (h3 : 3≤p)
    (hx : 0<x) (hy : 0<y) (hc : IsCoprime x y) (he : x^p+y^p=z^p)
    (hxz : x<z) (hyz : y<z) (hnx : ¬(p:ℤ)∣x) (hny : ¬(p:ℤ)∣y) (hdz : (p:ℤ)∣z) :
    ((p:ℤ)+1)^p<2*z := by
  have ho := hp.odd_of_ne_two (by omega)
  have hP := Nat.prime_iff_prime_int.mp hp
  have hz : 0<z := by omega
  have hzx := pair_zx (z:=z) hp h3 hc hz he
  have hzy := pair_zx (z:=z) hp h3 hc.symm hz (by rwa [add_comm])
  obtain ⟨b,_,hbp,_⟩ := root_factor hp h3 hzx (by rw [ho.neg_pow]; linarith) (by omega) hny
  obtain ⟨c,_,hcp,_⟩ := root_factor hp h3 hzy (by rw [ho.neg_pow]; linarith) (by omega) hnx
  have fin : FiniteMultiplicity (p:ℤ) (-z) := Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.ne_one,by omega⟩
  let k := multiplicity (p:ℤ) (-z)
  obtain ⟨v,hv,hnv⟩ := fin.exists_eq_pow_mul_and_not_dvd
  change -z=(p:ℤ)^k*v at hv
  have hk : 0<k := by
    by_contra! h
    rw [show k=0 by omega,pow_zero,one_mul] at hv
    exact hnv (hv ▸ dvd_neg.mpr hdz)
  obtain ⟨hd,_,_,dec⟩ := lemma56iii hp h3 hc (t := -z) (by rw [ho.neg_pow,he]; ring) (dvd_neg.mpr hdz)
  obtain ⟨w,_,_,_,hw,_,_⟩ := dec k v hk hnv hv
  have hkp : 2≤k*p-1 := by have := Nat.mul_le_mul_right p hk; omega
  have hdxy : (p:ℤ)^2 ∣ x+y := hw ▸ dvd_mul_of_dvd_left (pow_dvd_pow _ hkp) _
  have hbc : (p:ℤ)∣b+c := by
    have hm := (modp_pow hp b).add (modp_pow hp c)
    rw [← hbp,← hcp] at hm
    apply Int.modEq_zero_iff_dvd.mp (hm.symm.trans (Int.modEq_zero_iff_dvd.mpr ?_))
    rw [show z+ -x+(z+ -y)=2*z-(x+y) by ring]
    exact dvd_sub (dvd_mul_of_dvd_right hdz _) hd
  have hq : (p:ℤ)∣quotient b c p := dvd_geom_sum₂_self (x:=b) (y := -c) (by simpa using hbc)
  have hbc2 : (p:ℤ)^2∣b^p+c^p := by rw [← factor _ _ ho,pow_two]; exact mul_dvd_mul hbc hq
  have hz2 : (p:ℤ)^2∣2*z := by
    rw [show 2*z=(b^p+c^p)+(x+y) by omega]
    exact dvd_add hbc2 hdxy
  have hk2 : 2≤k := by
    by_contra! hk'
    rw [show k=1 by omega,pow_one] at hv
    obtain ⟨m,hm⟩ := hz2
    have hdiv : (p:ℤ)∣2*v := ⟨-m, by
      apply mul_left_cancel₀ hP.ne_zero
      linear_combination -2*hv - hm⟩
    rcases hP.dvd_or_dvd hdiv with h | h
    · have : p ∣ 2 := by exact_mod_cast h
      have := Nat.le_of_dvd (by decide : 0<2) this
      omega
    · exact hnv h
  have hwp : 0<w^p := by
    have hh : 0<(p:ℤ)^(k*p-1)*w^p := hw ▸ (show 0<x+y by omega)
    exact pos_of_mul_pos_right hh (by positivity)
  have hbig : (p:ℤ)^(2*p-1)≤x+y := by
    have hle := Nat.mul_le_mul_right p hk2
    calc
      (p:ℤ)^(2*p-1) ≤ (p:ℤ)^(k*p-1) := pow_le_pow_right₀ (by omega) (by omega)
      _ ≤ (p:ℤ)^(k*p-1)*w^p := le_mul_of_one_le_right (by positivity) (by omega)
      _ = _ := hw.symm
  linarith [threshold_power h3]

/-- Lemma 5.7. Cross multiplication retains the strict rational bound. -/
theorem lemma57 {p : ℕ} {x y z : ℤ} (hp : p.Prime) (h3 : 3≤p)
    (hx : 0<x) (hy : 0<y) (_hz : 0<z) (hc : IsCoprime x y) (he : x^p+y^p=z^p) :
    ((p:ℤ)+1)^p < 2*z := by
  have ho := hp.odd_of_ne_two (by omega)
  have hxz : x<z := ho.strictMono_pow.lt_iff_lt.mp (by linarith [pow_pos hy p])
  have hyz : y<z := ho.strictMono_pow.lt_iff_lt.mp (by linarith [pow_pos hx p])
  have htri : z≤x+y := ho.strictMono_pow.le_iff_le.mp (he ▸ pow_add_pow_le hx.le hy.le hp.ne_zero)
  by_cases hdx : (p:ℤ)∣x
  · exact divides_x_case hp h3 hx hy hc he hxz hyz htri hdx
  by_cases hdy : (p:ℤ)∣y
  · exact divides_x_case hp h3 hy hx hc.symm (by rwa [add_comm]) hyz hxz (by omega) hdy
  by_cases hdz : (p:ℤ)∣z
  · exact divides_z_case hp h3 hx hy hc he hxz hyz hdx hdy hdz
  · exact prime_to_xyz hp h3 hx hy hc he hxz hyz htri hdx hdy hdz

end ExpEst
