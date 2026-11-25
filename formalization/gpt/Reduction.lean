import Selection
namespace ExpEstL3
open Real Finset
noncomputable section

/-- The numerical replacements in the proof of 5.1 on pp. 34–35.
    The prime-counting comparison is Proposition 2.2(i) at x=e*l. -/
theorem coefficients51 {l e : ℝ} (hl : 10^15≤l) (he : δ≤e)
    (πbound : ((primesTo (e*l)).card:ℝ) ≤ 1.022*(e*l)/log (e*l)) :
    5*10^20≤e*l ∧ ((primesTo (e*l)).card:ℝ)*log (e*l)≤1.022*(e*l) ∧
    4*(l+5)/(l+1)≤4+1/10^13 ∧
    2*log l+56≤(1/10^5)*1.022*e*l ∧
    (4+1/10^13+1/10^5:ℝ)*1.022≤4.08803 := by
  have l0 : 0<l := lt_of_lt_of_le (by norm_num) hl
  have E : 5*10^20≤e*l := (show (5:ℝ)*10^20≤δ*10^15 by norm_num [δ]).trans
    (mul_le_mul he hl (by norm_num) ((by norm_num [δ] : (0:ℝ)≤δ).trans he))
  refine ⟨E,(le_div_iff₀ (log_pos (lt_of_lt_of_le (by norm_num) E))).mp πbound,?_,?_,by norm_num⟩
  · apply (div_le_iff₀ (by linarith)).mpr
    linarith only [hl]
  · have r : 3≤(1/10^5)*1.022*e := by dsimp [δ] at he; linarith only [he]
    have t := mul_le_mul_of_nonneg_right r l0.le
    linarith only [t,Real.log_le_self l0.le,hl]

/-- The displayed C_Θ, p. 34. There |log(q-underlined)| = q/(2l),
    where q below denotes the restricted logarithmic degree itself. -/
def thetaConstant (q B l : ℝ) : ℝ :=
  (l+1)/(4*(q/(2*l))) * ((1+12/l)*B + 4.08803*δ*l - (1-12/l^2)*(q/6)) - 1

theorem theta51_iff {q B l : ℝ} (hq : 0<q) (hl : 0<l) :
    -1≤thetaConstant q B l ↔ (1-12/l^2)*(q/6)≤(1+12/l)*B+4.08803*δ*l := by
  have hp : 0<(l+1)/(4*(q/(2*l))) := by positivity
  unfold thetaConstant
  constructor
  · intro hc
    apply sub_nonneg.mp
    exact nonneg_of_mul_nonneg_right (by linarith only [hc]) hp
  · intro h
    have hh := mul_nonneg hp.le (sub_nonneg.mpr h)
    linarith only [hh]

/-- Remove the factor (1-12/l²) from the Θ-constant inequality (p. 34).
    For L=ℚ we have d_mod=e_mod=1 and e_mod*=δ. -/
theorem estimate51 {q B l : ℝ} (hl : 10^15≤l) (hB : 0≤B)
    (input : (1-12/l^2)*(q/6) ≤ (1+12/l)*B+4.08803*δ*l) :
    q/6 ≤ (1+20/l)*B+4.0881*δ*l := by
  have l0 : 0<l := lt_of_lt_of_le (by norm_num) hl
  have l2 : l≤l^2 := by nlinarith only [mul_nonneg l0.le (show 0≤l-1 by linarith only [hl])]
  have hd : 0<1-12/l^2 := sub_pos.mpr ((div_lt_one (sq_pos_of_pos l0)).mpr (by linarith only [l2,hl]))
  have c₁ : 1+12/l ≤ (1-12/l^2)*(1+20/l) := by
    field_simp
    nlinarith only [mul_nonneg (sq_nonneg l) (show 0≤l-100 by linarith only [hl]),l2,hl]
  have c₂ : 4.08803 ≤ (1-12/l^2)*4.0881 := by
    field_simp
    nlinarith only [l2,hl]
  apply le_of_mul_le_mul_left (a := 1-12/l^2) _ hd
  apply input.trans
  nlinarith only [mul_le_mul_of_nonneg_right c₁ hB,
    mul_le_mul_of_nonneg_right c₂ (show 0≤δ*l by positivity)]

namespace LocalData
def Away (T : LocalData) (l : ℕ) : Prop := ∃ v∈T.places, T.p v≠l

lemma restricted_pos (T : LocalData) {l : ℕ} (ha : T.Away l) : 0<T.restricted l := by
  obtain ⟨v,hv,hp⟩ := ha
  have hmem : v∈T.places.filter (fun v => T.p v≠l) := mem_filter.mpr ⟨hv,hp⟩
  have wpos : 0<T.weight v := mul_pos (mul_pos (by exact_mod_cast T.npos v hv)
    (by exact_mod_cast T.fpos v hv)) (log_pos (by exact_mod_cast (T.prime v hv).one_lt))
  exact div_pos (wpos.trans_le (single_le_sum (fun i _ => T.weight_nonneg i) hmem))
    (by exact_mod_cast T.deg_pos)

/-- Splitting the height over the place l and its complement, p. 40. -/
theorem loss (T : LocalData) {l : ℕ} (E : T.Eligible l) :
    T.height - T.restricted l ≤ √T.height * log (l:ℝ) := by
  let S := T.places.filter (fun v => T.p v=l)
  have lp : 0≤log (l:ℝ) := log_nonneg (by exact_mod_cast E.1.one_le)
  have dl : 0<(T.degree:ℝ) := by exact_mod_cast T.deg_pos
  have split := Finset.sum_filter_add_sum_filter_not T.places (fun v => T.p v=l) T.weight
  have fibreWeight : (∑ v ∈ S, T.weight v) ≤ √T.height * log (l:ℝ) * T.degree := by
    calc
      _ ≤ ∑ v ∈ S, (√T.height * log (l:ℝ)) * T.f v := by
        apply sum_le_sum
        intro v hv
        obtain ⟨hv',hpl⟩ := mem_filter.mp hv
        have hvn := (E.2.2.2.2 v hv' hpl).le
        unfold weight
        rw [hpl]
        calc
          _ = (T.n v:ℝ)*(T.f v*log (l:ℝ)) := by ring
          _ ≤ √T.height*(T.f v*log (l:ℝ)) := mul_le_mul_of_nonneg_right hvn (mul_nonneg (by positivity) lp)
          _ = _ := by ring
      _ = √T.height * log (l:ℝ) * (∑ v ∈ S, (T.f v:ℝ)) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast T.fibre l) (mul_nonneg (sqrt_nonneg _) lp)
  unfold height restricted
  rw [←sub_div]
  apply (div_le_iff₀ dl).mpr
  change (∑ v ∈ S,T.weight v) + _ = _ at split
  change _ ≤ √T.height * log (l:ℝ) * T.degree
  rw [←split,add_sub_cancel_right]
  exact fibreWeight

theorem away_of_large (T : LocalData) {l : ℕ} (H : 10^30≤T.height) (E : T.Eligible l) :
    T.Away l := by
  by_contra hn
  have hempty : T.places.filter (fun v => T.p v≠l) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hn ⟨v,(mem_filter.mp hv).1,(mem_filter.mp hv).2⟩
  have hh := T.loss E
  rw [restricted,hempty,sum_empty,zero_div,sub_zero] at hh
  have s0 : 0<√T.height := lt_of_lt_of_le (by norm_num) (sqrt_large H)
  have hi := (prime_log_bounds H (by exact_mod_cast E.1.pos) E.2.2.1).1
  have hs2 := sq_sqrt (show 0≤T.height from (by norm_num : (0:ℝ)≤10^30).trans H)
  have hlog : √T.height ≤ log (l:ℝ) := by
    apply le_of_mul_le_mul_left (a := √T.height) _ s0
    rwa [←sq,hs2]
  linarith only [hlog,hi,f_positive H]

/-- The conclusion preceding (P8), retaining the loss over l explicitly. -/
theorem p8 (T : LocalData) {l : ℕ} {B : ℝ} (H : 10^30≤T.height) (E : T.Eligible l)
    (hB : 0≤B) (h51 : T.restricted l / 6 ≤ (1+20/(l:ℝ))*B+4.0881*δ*l) :
    T.height/6 * (1 - (log (l:ℝ) + 35.91*δ^2*log (scale*T.height))/√T.height)
       ≤ (1+δ/√T.height)*B := by
  let s := √T.height
  let L := log (scale*T.height)
  have s0 : 0<s := lt_of_lt_of_le (by norm_num) (sqrt_large H)
  have l0 : (0:ℝ)<l := by exact_mod_cast E.1.pos
  have hs2 : s^2=T.height := sq_sqrt ((by norm_num : (0:ℝ)≤10^30).trans H)
  have ht : 20/(l:ℝ) ≤ δ/s := by
    apply (div_le_div_iff₀ l0 s0).mpr
    exact (mul_le_mul_of_nonneg_right (by norm_num [δ] : (20:ℝ)≤δ) s0.le).trans
      (mul_le_mul_of_nonneg_left E.2.1 (by norm_num))
  have hB' := mul_le_mul_of_nonneg_right (add_le_add_right ht 1) hB
  have hU := mul_le_mul_of_nonneg_left E.2.2.1 (show (0:ℝ)≤4.0881*δ by norm_num)
  have hL : 0≤L := (show (0:ℝ)≤82.65 by norm_num).trans (log_large H)
  have round : 4.0881*δ*(1.464*δ*s*L) ≤ 5.985*δ^2*s*L := by
    have q := mul_le_mul_of_nonneg_right (by norm_num : (4.0881:ℝ)*1.464≤5.985)
      (mul_nonneg (mul_nonneg (sq_nonneg δ) s0.le) hL)
    linarith only [q]
  have loss' := T.loss E
  change T.height-T.restricted l ≤ s*log (l:ℝ) at loss'
  change _ ≤ (1+20/(l:ℝ))*B+4.0881*δ*l at h51
  have midway : T.height/6 ≤ (1+δ/s)*B + s*log (l:ℝ)/6 + 5.985*δ^2*s*L := by
    linarith only [loss',h51,hB',hU.trans round]
  change T.height/6*(1-(log (l:ℝ)+35.91*δ^2*L)/s) ≤ (1+δ/s)*B
  have cancel : T.height*((log (l:ℝ)+35.91*δ^2*L)/s) = s*(log (l:ℝ)+35.91*δ^2*L) := by
    rw [←hs2]; field_simp
  linarith only [midway,cancel]

/-- Claim 5.2B absorbs the error in (P8); this is (C2), before the
    external comparison of the log-different and log-conductor. -/
theorem c2_of_p8 (T : LocalData) {ε B : ℝ} {l : ℕ} (he : 0<ε) (hε : ε≤1)
    (H : ExpEstL2.hOne ε≤T.height) (E : T.Eligible l) (hP8 :
    T.height/6*(1-(log (l:ℝ)+35.91*δ^2*log (scale*T.height))/√T.height)
    ≤ (1+δ/√T.height)*B) : T.height/6 ≤ (1+ε)*B := by
  let x := (log (l:ℝ)+35.91*δ^2*log (scale*T.height))/√T.height
  let y := δ/√T.height
  have h0 : 10^30≤T.height := (show (10:ℝ)^30≤baseH by norm_num).trans ((base_le_hOne he hε).trans H)
  have L := (show (0:ℝ)≤82.65 by norm_num).trans (log_large h0)
  have x0 : 0≤x := div_nonneg (add_nonneg (lp l E.1) (mul_nonneg (by norm_num) L)) (sqrt_nonneg _)
  have y0 : 0≤y := div_nonneg (by norm_num) (sqrt_nonneg _)
  have hb := claim52B he hε H (show (0:ℝ)<l by exact_mod_cast E.1.pos) E.2.2.1
  have xy : 2*x+y≤ε := by
    apply le_trans _ hb
    dsimp only [x,y]; ring_nf; rfl
  have pos : 0<1-x := by linarith only [xy,hε,y0]
  have c : 1+y≤(1+ε)*(1-x) := by nlinarith only [xy,mul_nonneg (sub_nonneg.mpr hε) x0]
  change T.height/6*(1-x) ≤ (1+y)*B at hP8
  have hB : 0≤B := by
    by_contra! hn
    have neg := mul_neg_of_pos_of_neg (by linarith : 0<1+y) hn
    have hn' : 0≤T.height/6*(1-x) := mul_nonneg (by linarith only [h0,show (0:ℝ)≤10^30 by norm_num]) pos.le
    linarith
  apply le_of_mul_le_mul_right (a := 1-x) _ pos
  calc
    _ ≤ (1+y)*B := hP8
    _ ≤ ((1+ε)*(1-x))*B := mul_le_mul_of_nonneg_right c hB
    _ = _ := by ring
where
  lp (p : ℕ) (hp : p.Prime) : 0≤log (p:ℝ) := log_nonneg (by exact_mod_cast hp.one_le)

end LocalData
end
end ExpEstL3
