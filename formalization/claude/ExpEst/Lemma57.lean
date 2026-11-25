import ExpEst.Lemma56

/-!
# ExpEst Lemma 5.7

Let `p ≥ 3` be prime and `x, y, z` coprime positive integers with `x^p + y^p = z^p`.
Then `z > (p+1)^p / 2`, stated here as `(p + 1)^p < 2 z`.

"Coprime" is taken as `IsCoprime x y`; under the Fermat relation this is equivalent to
`gcd(x, y, z) = 1`, and pairwise coprimality follows (`isCoprime_x_z`).
The proof follows the paper's three cases: `p ∣ xy`, `p ∤ xyz`, `p ∣ z`.
-/

namespace ExpEst

open Finset

variable {p : ℕ}

/-! ### Small helpers -/

theorem isCoprime_of_no_prime {a b : ℤ}
    (H : ∀ l : ℕ, l.Prime → (l : ℤ) ∣ a → (l : ℤ) ∣ b → False) : IsCoprime a b := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  apply Nat.coprime_of_dvd
  intro k hk h1 h2
  exact H k hk (Int.natCast_dvd.mpr h1) (Int.natCast_dvd.mpr h2)

/-- From `x^p + y^p = z^p` and `IsCoprime x y`: `IsCoprime x z`. -/
theorem isCoprime_x_z (hp0 : p ≠ 0) {x y z : ℤ} (hxy : IsCoprime x y)
    (h : x ^ p + y ^ p = z ^ p) : IsCoprime x z := by
  apply isCoprime_of_no_prime
  intro l hl h1 h2
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h3 : (l : ℤ) ∣ y ^ p := by
    have : y ^ p = z ^ p - x ^ p := by linarith
    rw [this]
    exact dvd_sub (dvd_pow h2 hp0) (dvd_pow h1 hp0)
  exact hlZ.not_unit (hxy.isUnit_of_dvd' h1 (hlZ.dvd_of_dvd_pow h3))

/-- `x^p + y^p < (2x + y)^p` for positive `x, y` and `p ≠ 0`. -/
theorem pow_add_pow_lt_two_mul_add (hp0 : p ≠ 0) {x y : ℤ} (hx : 0 < x) (hy : 0 < y) :
    x ^ p + y ^ p < (2 * x + y) ^ p := by
  calc x ^ p + y ^ p ≤ (x + y) ^ p := pow_add_pow_le hx.le hy.le hp0
    _ < (2 * x + y) ^ p := pow_lt_pow_left₀ (by linarith) (by linarith) hp0

/-- `p`-th roots of positive integers (Lemma 5.6 (ii) with positivity). -/
theorem root_pos (hp : p.Prime) (hodd : Odd p) {r s t : ℤ} (hrs : IsCoprime r s)
    (h : r ^ p + s ^ p + t ^ p = 0) (hpt : ¬ (p : ℤ) ∣ t) (hpos : 0 < r + s) :
    ∃ u u' : ℤ, 0 < u ∧ r + s = u ^ p ∧ Q p r s = u' ^ p ∧ t = -(u * u') := by
  obtain ⟨_, u, u', hu, hu', ht⟩ := lemma56_ii hp hodd hrs h hpt
  exact ⟨u, u', (Odd.pow_pos_iff hodd).mp (hu ▸ hpos), hu, hu', ht⟩

/-- Fermat's little theorem for integer casts into `ZMod p`. -/
theorem cast_pow_p (hp : p.Prime) (a : ℤ) : ((a ^ p : ℤ) : ZMod p) = (a : ZMod p) := by
  haveI := Fact.mk hp
  push_cast
  exact ZMod.pow_card _

/-- `Q p r s` is odd when `r, s` are odd (a sum of `p` odd terms, `p` odd). -/
theorem Q_odd (hodd : Odd p) {r s : ℤ} (hr : Odd r) (hs : Odd s) : Odd (Q p r s) := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hr1 : ((r : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hr
  have hs1 : ((-s : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hs.neg
  simp only [Q, Int.cast_sum, Int.cast_mul, Int.cast_pow, hr1, hs1, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact ZMod.natCast_eq_one_iff_odd.mpr hodd

/-- Parity contradiction used in Claim 5.7C (cases `E = {a}`, `{b}`, `{c}`):
if `r + s = m` with `m ≠ 0` even, `r, s` odd and `p ≥ 2` odd, then `r^p + s^p ≠ 2 m e - m^p`. -/
theorem parity_contra (hodd : Odd p) (hp1 : 2 ≤ p) {m r s e : ℤ} (hm : Even m) (hm0 : m ≠ 0)
    (hr : Odd r) (hs : Odd s) (hsum : r + s = m) (heq : r ^ p + s ^ p = 2 * m * e - m ^ p) :
    False := by
  have hQ : Q p r s = 2 * e - m ^ (p - 1) := by
    apply mul_left_cancel₀ hm0
    have hmp : m ^ p = m * m ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hsum, add_mul_Q hodd, heq, hsum, hmp]
    ring
  have hev : Even (2 * e - m ^ (p - 1)) :=
    (even_two_mul e).sub (hm.pow_of_ne_zero (by omega))
  rw [← hQ] at hev
  exact (Int.not_even_iff_odd.mpr (Q_odd hodd hr hs)) hev

/-- `(p + 1)^p < p^(2p - 1)` for `p ≥ 3`. -/
theorem succ_pow_lt (hp3 : 3 ≤ p) : (p + 1) ^ p < p ^ (2 * p - 1) := by
  have h1 : (2 * (p + 1)) ^ p ≤ (p ^ 2) ^ p := Nat.pow_le_pow_left (by nlinarith) p
  have h2 : p < 2 ^ p := Nat.lt_two_pow_self
  have h3 : p ^ (2 * p) = p * p ^ (2 * p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [mul_pow, ← pow_mul, h3] at h1
  by_contra hc
  push Not at hc
  have hpos : 0 < p ^ (2 * p - 1) := pow_pos (by omega) _
  have : 2 ^ p * (p + 1) ^ p < 2 ^ p * (p + 1) ^ p :=
    calc 2 ^ p * (p + 1) ^ p ≤ p * p ^ (2 * p - 1) := h1
      _ < 2 ^ p * p ^ (2 * p - 1) := Nat.mul_lt_mul_of_pos_right h2 hpos
      _ ≤ 2 ^ p * (p + 1) ^ p := Nat.mul_le_mul_left _ hc
  exact lt_irrefl _ this

/-! ### The three cases -/

section cases

variable (hp : p.Prime) (hodd : Odd p) {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hxy : IsCoprime x y) (h : x ^ p + y ^ p = z ^ p)
include hp hodd hx hy hz hxy h

omit hodd hxy in
theorem lt_z_of_fermat : x < z ∧ y < z := by
  have hp0 := hp.ne_zero
  constructor
  · apply lt_of_pow_lt_pow_left₀ p hz.le
    have : 0 < y ^ p := pow_pos hy p
    linarith
  · apply lt_of_pow_lt_pow_left₀ p hz.le
    have : 0 < x ^ p := pow_pos hx p
    linarith

/-- Case `p ∣ x` of Lemma 5.7. -/
theorem lemma57_case_px (hpx : (p : ℤ) ∣ x) : ((p : ℤ) + 1) ^ p < 2 * z := by
  have hp0 := hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hxz := isCoprime_x_z hp0 hxy h
  have hpz : ¬ (p : ℤ) ∣ z := fun hpz => hpZ.not_unit (hxz.isUnit_of_dvd' hpx hpz)
  have hpy : ¬ (p : ℤ) ∣ y := fun hpy => hpZ.not_unit (hxy.isUnit_of_dvd' hpx hpy)
  obtain ⟨hzx, hzy⟩ := lt_z_of_fermat hp hx hy hz h
  have T1 : x ^ p + y ^ p + (-z) ^ p = 0 := by rw [Odd.neg_pow hodd]; linarith
  have T2 : z ^ p + (-x) ^ p + (-y) ^ p = 0 := by
    rw [Odd.neg_pow hodd, Odd.neg_pow hodd]; linarith
  obtain ⟨a, -, ha, hxa, -, -⟩ :=
    root_pos hp hodd hxy T1 (by rwa [dvd_neg]) (by linarith)
  obtain ⟨b, -, hb, hzb, -, -⟩ :=
    root_pos hp hodd hxz.symm.neg_right T2 (by rwa [dvd_neg]) (by linarith)
  -- b ≡ a (mod p)
  have hba : (p : ℤ) ∣ b - a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have ea := congrArg (Int.cast : ℤ → ZMod p) hxa
    have eb := congrArg (Int.cast : ℤ → ZMod p) hzb
    have eh := congrArg (Int.cast : ℤ → ZMod p) h
    rw [cast_pow_p hp] at ea eb
    rw [Int.cast_add, cast_pow_p hp, cast_pow_p hp, cast_pow_p hp] at eh
    have hx0 : ((x : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mpr hpx
    push_cast at ea eb ⊢
    rw [← ea, ← eb]
    linear_combination (-1 : ZMod p) * eh + (-1 : ZMod p) * hx0
  -- Claim 5.7A: max{a, b} ≥ p + 1
  have hmax : (p : ℤ) + 1 ≤ a ∨ (p : ℤ) + 1 ≤ b := by
    by_contra hc
    push Not at hc
    obtain ⟨ha', hb'⟩ := hc
    have hab0 : b - a = 0 :=
      Int.eq_zero_of_abs_lt_dvd hba (by rw [abs_lt]; constructor <;> linarith)
    have hab : b = a := by linarith
    rw [hab] at hzb
    have hz2 : z = 2 * x + y := by linarith
    have := pow_add_pow_lt_two_mul_add hp0 hx hy
    rw [← hz2, h] at this
    exact lt_irrefl _ this
  -- 2z > z + y = a^p + b^p ≥ (p + 1)^p
  have hap : 0 < a ^ p := pow_pos ha p
  have hbp : 0 < b ^ p := pow_pos hb p
  rcases hmax with h1 | h1
  · have : ((p : ℤ) + 1) ^ p ≤ a ^ p := pow_le_pow_left₀ (by positivity) h1 p
    linarith
  · have : ((p : ℤ) + 1) ^ p ≤ b ^ p := pow_le_pow_left₀ (by positivity) h1 p
    linarith

/-- Case `p ∤ xyz` of Lemma 5.7 (Claims 5.7B, 5.7C). -/
theorem lemma57_case_none (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y) (hpz : ¬ (p : ℤ) ∣ z) :
    ((p : ℤ) + 1) ^ p < 2 * z := by
  have hp0 := hp.ne_zero
  have hp2 : 2 ≤ p := hp.two_le
  have hxz := isCoprime_x_z hp0 hxy h
  have hyz := isCoprime_x_z hp0 hxy.symm (by linarith : y ^ p + x ^ p = z ^ p)
  obtain ⟨hzx, hzy⟩ := lt_z_of_fermat hp hx hy hz h
  have T1 : x ^ p + y ^ p + (-z) ^ p = 0 := by rw [Odd.neg_pow hodd]; linarith
  have T2 : z ^ p + (-x) ^ p + (-y) ^ p = 0 := by
    rw [Odd.neg_pow hodd, Odd.neg_pow hodd]; linarith
  have T3 : z ^ p + (-y) ^ p + (-x) ^ p = 0 := by
    rw [Odd.neg_pow hodd, Odd.neg_pow hodd]; linarith
  obtain ⟨a, a', ha, hxa, -, hza⟩ :=
    root_pos hp hodd hxy T1 (by rwa [dvd_neg]) (by linarith)
  obtain ⟨b, b', hb, hzb, -, hyb⟩ :=
    root_pos hp hodd hxz.symm.neg_right T2 (by rwa [dvd_neg]) (by linarith)
  obtain ⟨c, c', hc, hzc, -, hxc⟩ :=
    root_pos hp hodd hyz.symm.neg_right T3 (by rwa [dvd_neg]) (by linarith)
  -- b + c - a ≡ 2 (z - x - y) ≡ 0 (mod p)
  have hbca : (p : ℤ) ∣ b + c - a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have ea := congrArg (Int.cast : ℤ → ZMod p) hxa
    have eb := congrArg (Int.cast : ℤ → ZMod p) hzb
    have ec := congrArg (Int.cast : ℤ → ZMod p) hzc
    have eh := congrArg (Int.cast : ℤ → ZMod p) h
    rw [cast_pow_p hp] at ea eb ec
    rw [Int.cast_add, cast_pow_p hp, cast_pow_p hp, cast_pow_p hp] at eh
    push_cast at ea eb ec ⊢
    rw [← ea, ← eb, ← ec]
    linear_combination (-2 : ZMod p) * eh
  -- Claim 5.7B: a ≥ p + 1
  have hA : (p : ℤ) + 1 ≤ a := by
    by_contra hcon
    push Not at hcon
    have hz2x : z < 2 * x + y := by
      have := pow_add_pow_lt_two_mul_add hp0 hx hy
      rw [h] at this
      exact lt_of_pow_lt_pow_left₀ p (by linarith) this
    have hz2y : z < 2 * y + x := by
      have := pow_add_pow_lt_two_mul_add hp0 hy hx
      rw [add_comm, h] at this
      exact lt_of_pow_lt_pow_left₀ p (by linarith) this
    have hab : b < a := by
      apply lt_of_pow_lt_pow_left₀ p ha.le
      rw [← hxa, ← hzb]
      linarith
    have hac : c < a := by
      apply lt_of_pow_lt_pow_left₀ p ha.le
      rw [← hxa, ← hzc]
      linarith
    have h0 : b + c - a = 0 :=
      Int.eq_zero_of_abs_lt_dvd hbca (by rw [abs_lt]; constructor <;> linarith)
    have hsum : b + c = a := by linarith
    -- Claim 5.7C and the parity contradictions
    rcases Int.even_or_odd b with hbe | hbo <;> rcases Int.even_or_odd c with hce | hco
    · -- a, b, c all even: then x, y, z are all odd, impossible
      have hae : Even a := hsum ▸ hbe.add hce
      have hxy2 : Even (x + y) := hxa ▸ hae.pow_of_ne_zero hp0
      have hzx2 : Even (z + -x) := hzb ▸ hbe.pow_of_ne_zero hp0
      rcases Int.even_or_odd x with hxe | hxo
      · have hye : Even y := by
          have := hxy2.sub hxe
          simpa using this
        have hu := hxy.isUnit_of_dvd' (even_iff_two_dvd.mp hxe) (even_iff_two_dvd.mp hye)
        norm_num [Int.isUnit_iff] at hu
      · have hyo : Odd y := by
          have := hxy2.sub_odd hxo
          simpa using this
        have hzo : Odd z := by
          have := hzx2.add_odd hxo
          simpa using this
        have : Even (z ^ p) := h ▸ (hxo.pow.add_odd hyo.pow)
        exact (Int.not_even_iff_odd.mpr hzo.pow) this
    · -- E = {b}
      have hao : Odd a := hsum ▸ hbe.add_odd hco
      apply parity_contra hodd hp2 (m := b) (r := a) (s := -c) (e := b') hbe hb.ne' hao hco.neg
        (by linarith)
      rw [Odd.neg_pow hodd, ← hxa, ← hzc, ← hzb]
      linear_combination (-2 : ℤ) * hyb
    · -- E = {c}
      have hao : Odd a := hsum ▸ hbo.add_even hce
      apply parity_contra hodd hp2 (m := c) (r := a) (s := -b) (e := c') hce hc.ne' hao hbo.neg
        (by linarith)
      rw [Odd.neg_pow hodd, ← hxa, ← hzb, ← hzc]
      linear_combination (-2 : ℤ) * hxc
    · -- E = {a}
      have hae : Even a := hsum ▸ hbo.add_odd hco
      apply parity_contra hodd hp2 (m := a) (r := b) (s := c) (e := a') hae ha.ne' hbo hco hsum
      rw [← hzb, ← hzc, ← hxa]
      linear_combination (-2 : ℤ) * hza
  -- 2z > x + y = a^p ≥ (p + 1)^p
  have : ((p : ℤ) + 1) ^ p ≤ a ^ p := pow_le_pow_left₀ (by positivity) hA p
  linarith

/-- Case `p ∣ z` of Lemma 5.7. -/
theorem lemma57_case_pz (hpz : (p : ℤ) ∣ z) (hp3 : 3 ≤ p) : ((p : ℤ) + 1) ^ p < 2 * z := by
  have hp0 := hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0Z : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hxz := isCoprime_x_z hp0 hxy h
  have hyz := isCoprime_x_z hp0 hxy.symm (by linarith : y ^ p + x ^ p = z ^ p)
  have hpx : ¬ (p : ℤ) ∣ x := fun hpx => hpZ.not_unit (hxz.isUnit_of_dvd' hpx hpz)
  have hpy : ¬ (p : ℤ) ∣ y := fun hpy => hpZ.not_unit (hyz.isUnit_of_dvd' hpy hpz)
  obtain ⟨hzx, hzy⟩ := lt_z_of_fermat hp hx hy hz h
  have T1 : x ^ p + y ^ p + (-z) ^ p = 0 := by rw [Odd.neg_pow hodd]; linarith
  have T2 : z ^ p + (-x) ^ p + (-y) ^ p = 0 := by
    rw [Odd.neg_pow hodd, Odd.neg_pow hodd]; linarith
  have T3 : z ^ p + (-y) ^ p + (-x) ^ p = 0 := by
    rw [Odd.neg_pow hodd, Odd.neg_pow hodd]; linarith
  obtain ⟨b, -, hb, hzb, -, -⟩ :=
    root_pos hp hodd hxz.symm.neg_right T2 (by rwa [dvd_neg]) (by linarith)
  obtain ⟨c, -, hc, hzc, -, -⟩ :=
    root_pos hp hodd hyz.symm.neg_right T3 (by rwa [dvd_neg]) (by linarith)
  -- z = p^k v0 with p ∤ v0
  have hfin : FiniteMultiplicity (p : ℤ) z :=
    Int.finiteMultiplicity_iff.mpr ⟨by simp [hp.one_lt.ne'], hz.ne'⟩
  obtain ⟨v0, hzv, hpv0⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set k := multiplicity (p : ℤ) z with hkdef
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero, one_mul] at hzv
      exact absurd (hzv ▸ hpz) hpv0
    · exact hk0
  -- Lemma 5.6 (iii) for (x, y, -z): x + y = p^(kp-1) w^p
  have hpmz : (p : ℤ) ∣ -z := dvd_neg.mpr hpz
  obtain ⟨hpxy, -, -⟩ := lemma56_iii hp hodd hxy (neg_ne_zero.mpr hz.ne') T1 hpmz
  obtain ⟨w, -, -, -, hxyw, -, -⟩ :=
    lemma56_iii' hp hodd hxy (neg_ne_zero.mpr hz.ne') T1 hk (v := -v0)
      (by rwa [dvd_neg]) (by rw [hzv]; ring)
  -- b + c ≡ 2z - (x + y) ≡ 0 (mod p)
  have hpbc : (p : ℤ) ∣ b + c := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have eb := congrArg (Int.cast : ℤ → ZMod p) hzb
    have ec := congrArg (Int.cast : ℤ → ZMod p) hzc
    rw [cast_pow_p hp] at eb ec
    have hz0 : ((z : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr hpz
    have hxy0 : ((x + y : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpxy
    push_cast at eb ec hxy0 ⊢
    rw [← eb, ← ec]
    linear_combination (2 : ZMod p) * hz0 - hxy0
  -- p² ∣ b^p + c^p (Lemma 5.5)
  have hp2bc : (p : ℤ) ^ 2 ∣ b ^ p + c ^ p := by
    obtain ⟨m, hm⟩ := lemma55 hodd b c
    obtain ⟨n, hn⟩ := hpbc
    rw [← add_mul_Q hodd]
    have : Q p b c = p * c ^ (p - 1) + (b + c) * m := by linarith
    rw [this, hn]
    exact ⟨n * c ^ (p - 1) + n * n * m, by ring⟩
  -- k ≥ 2
  have hk2 : 2 ≤ k := by
    by_contra hcon
    push Not at hcon
    have hk1 : k = 1 := by omega
    have e2z : 2 * z = (b ^ p + c ^ p) + (x + y) := by linarith
    have hp2xy : (p : ℤ) ^ 2 ∣ x + y := by
      rw [hxyw, hk1, one_mul]
      exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
    have hp2z : (p : ℤ) ^ 2 ∣ 2 * z := e2z ▸ dvd_add hp2bc hp2xy
    rw [hzv, hk1, pow_one] at hp2z
    have h2v : (p : ℤ) ∣ 2 * v0 := by
      obtain ⟨q, hq⟩ := hp2z
      exact ⟨q, by apply mul_left_cancel₀ hp0Z; linear_combination hq⟩
    rcases hpZ.dvd_or_dvd h2v with h2 | h2
    · have := Int.le_of_dvd (by norm_num) h2
      omega
    · exact hpv0 h2
  -- x + y ≥ p^(2p-1)
  have hpk : 0 < (p : ℤ) ^ (k * p - 1) := pow_pos (by exact_mod_cast hp.pos) _
  have hwp : 0 < w ^ p := by
    have : 0 < (p : ℤ) ^ (k * p - 1) * w ^ p := hxyw ▸ (by linarith)
    exact pos_of_mul_pos_right this hpk.le
  have hxy_ge : (p : ℤ) ^ (2 * p - 1) ≤ x + y := by
    rw [hxyw]
    calc (p : ℤ) ^ (2 * p - 1) ≤ (p : ℤ) ^ (k * p - 1) :=
          pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le)
            (Nat.sub_le_sub_right (Nat.mul_le_mul_right p hk2) 1)
      _ = (p : ℤ) ^ (k * p - 1) * 1 := (mul_one _).symm
      _ ≤ (p : ℤ) ^ (k * p - 1) * w ^ p := mul_le_mul_of_nonneg_left (by linarith) hpk.le
  have hfin2 : ((p : ℤ) + 1) ^ p < (p : ℤ) ^ (2 * p - 1) := by exact_mod_cast succ_pow_lt hp3
  linarith

end cases

/-- **Lemma 5.7.** For a prime `p ≥ 3` and coprime positive integers with
`x^p + y^p = z^p`, we have `z > (p + 1)^p / 2`. -/
theorem lemma57 {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hxy : IsCoprime x y) (h : x ^ p + y ^ p = z ^ p) :
    ((p : ℤ) + 1) ^ p < 2 * z := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases hpx : (p : ℤ) ∣ x
  · exact lemma57_case_px hp hodd hx hy hz hxy h hpx
  by_cases hpy : (p : ℤ) ∣ y
  · exact lemma57_case_px hp hodd hy hx hz hxy.symm (by linarith) hpy
  by_cases hpz : (p : ℤ) ∣ z
  · exact lemma57_case_pz hp hodd hx hy hz hxy h hpz hp3
  · exact lemma57_case_none hp hodd hx hy hz hxy h hpx hpy hpz

end ExpEst
