import ExpEst.L2

/-!
# L2: global forms, the link to L1, and audit examples
-/

namespace ExpEst

open Real Height

/-- Theorem 5.3 (ii) for `L = ℚ` and a given `ε` (both inequalities). -/
def Thm53ii_Q_eps (ε : ℝ) : Prop :=
  ∀ a b c : ℚ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 →
    mulHeight ![a, b, c] ≤
        2 ^ ((5 : ℝ) / 2) * max (exp (h1 ε / 4)) (radQ a b c ^ (3 * (1 + ε) / 2)) ∧
      2 ^ ((5 : ℝ) / 2) * max (exp (h1 ε / 4)) (radQ a b c ^ (3 * (1 + ε) / 2)) ≤
        2 ^ ((5 : ℝ) / 2) * exp (h1 ε / 4) * radQ a b c ^ (3 * (1 + ε) / 2)

/-- Theorem 5.4 for a given `ε` (both inequalities). -/
def Thm54_eps (ε : ℝ) : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 → IsCoprime a b →
    |((a * b * c : ℤ) : ℝ)| ≤
        2 ^ 4 * max (exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81))) ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε))) ∧
      2 ^ 4 * max (exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81))) ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε))) ≤
        2 ^ 4 * exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81)) * (rad (a * b * c) : ℝ) ^ (3 * (1 + ε))

/-- Theorem 5.3: (i) ⇒ (ii) over `ℚ`, for every `0 < ε`. -/
theorem thm53_i_imp_ii {ε : ℝ} (hε : 0 < ε) (H : Thm53i_Q ε) : Thm53ii_Q_eps ε :=
  fun a b c ha hb hc habc => thm53ii_of_i hε ha hb hc habc (H a b c ha hb hc habc)

/-- Theorem 5.3 (i) ⇒ Theorem 5.4, for every `0 < ε`. -/
theorem thm53i_imp_thm54 {ε : ℝ} (hε : 0 < ε) (H : Thm53i_Q ε) : Thm54_eps ε :=
  fun a b c ha hb hc habc hcop => thm54 hε ha hb hc habc hcop (H a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast habc))

/-- For `ε = 1`, the first inequality of (ii) is the hypothesis `Thm53ii_Q` of Corollary 5.8 (L1).
The two are mathematically the same statement; this direction is the one used. -/
theorem thm53ii_Q_of_eps_one (H : Thm53ii_Q_eps 1) : Thm53ii_Q := by
  intro a b c ha hb hc habc
  have h := (H a b c ha hb hc habc).1
  have e : (3 * (1 + (1 : ℝ)) / 2) = ((3 : ℕ) : ℝ) := by norm_num
  rw [e, rpow_natCast] at h
  exact h

/-- **Corollary 5.8 from Theorem 5.3 (i)** (`L = ℚ`, `ε = 1`). -/
theorem cor58_of_thm53i (H : Thm53i_Q 1) {p : ℕ} (hp : p.Prime)
    (hpbig : (1.615 * 10 ^ 14 : ℝ) < p) {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ p + y ^ p ≠ z ^ p :=
  cor58_Q (thm53ii_Q_of_eps_one (thm53_i_imp_ii one_pos H)) hp hpbig hx hy hz

/-! ## Audit examples -/

/-- The hypothesis of `thm53ii_of_i` holds at every triple with `h^non(j) ≤ h₁(ε)`; it is a
genuine restriction only for `h^non(j) > h₁(ε)`.  (For positive `ε`, `h₁(ε) ≥ 3.4·10^30` iff `ε ≤ 1`.) -/
theorem thm53i_small {ε : ℝ} {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : a + b + c = 0)
    (hsmall : hnon (@WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc)) ≤ h1 ε) :
    (1 / 6 : ℝ) * hnon (@WeierstrassCurve.j ℚ _ (Eabc a b c) (Eabc_isElliptic ha hb hc habc)) ≤
      max ((1 + ε) * Real.log (radQ a b c)) ((1 / 6 : ℝ) * h1 ε) :=
  le_trans (by linarith) (le_max_right _ _)

/-- `j(E_{1,1,-2}) = 1728` and `h^non(1728) = 0`. -/
theorem example_j : @WeierstrassCurve.j ℚ _ (Eabc 1 1 (-2))
    (Eabc_isElliptic one_ne_zero one_ne_zero (by norm_num) (by norm_num)) = 1728 := by
  rw [j_Eabc one_ne_zero one_ne_zero (by norm_num) (by norm_num)]
  norm_num

theorem example_hnon : hnon 1728 = 0 := by
  rw [hnon_eq_log_den]
  have : (1728 : ℚ).den = 1 := rfl
  rw [this]
  simp

end ExpEst
