import Numeric
import Mathlib.Data.Int.Interval
namespace ExpEstL3
open Real ExpEstL2
noncomputable section

def parameter (D : QTriple) : ℚ := -(D.a / D.c)
def exceptional (B : ℝ) : Set ℚ :=
  {x | ∃ D : QTriple, parameter D=x ∧ hNon D.curve.j≤B}

theorem mem_exceptional {B : ℝ} (D : QTriple) :
    parameter D ∈ exceptional B ↔ hNon D.curve.j ≤ B := by
  constructor
  · rintro ⟨D',he,h⟩
    have hr : D'.a/D'.c=D.a/D.c := neg_inj.mp he
    have hc : D'.curve=D.curve := by simp only [QTriple.curve,hr]
    have hj : D'.curve.j=D.curve.j := by congr 1
    rwa [hj] at h
  · exact fun H => ⟨D,rfl,H⟩

/-- The small-height exceptional set on the λ-line is finite even though
    the same point has infinitely many representatives (a,b,c). -/
theorem exceptional_finite (B : ℝ) : (exceptional B).Finite := by
  let N := ⌈exp (B/4+5/2*log 2)⌉₊
  let I := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let points := (I ×ˢ I).image (fun v : ℤ × ℤ => -((v.1:ℚ)/v.2))
  apply points.finite_toSet.subset
  rintro x ⟨D,rfl,H⟩
  have bound := claim53C D
  have hl : log D.height ≤ B/4+5/2*log 2 := by linarith only [bound,H]
  have hh := exp_le_exp.mpr hl
  rw [exp_log (by exact_mod_cast D.primitive.height_pos)] at hh
  have hN : D.height≤N := by exact_mod_cast hh.trans (Nat.le_ceil _)
  have coord (z : ℤ) (hz : z.natAbs ≤ D.height) : z∈I := by
    have hc : z.natAbs≤N := hz.trans hN
    change z∈Finset.Icc _ _
    rw [Finset.mem_Icc]
    omega
  have ha : D.primitive.a∈I := coord _ (le_max_left ..)
  have hc : D.primitive.c∈I := coord _ ((le_max_right ..).trans (le_max_right ..))
  apply Finset.mem_image.mpr
  refine ⟨(D.primitive.a,D.primitive.c),Finset.mem_product.mpr ⟨ha,hc⟩,?_⟩
  obtain ⟨k,hk,hka,_,hkc⟩ := D.scale_primitive
  dsimp [parameter]
  rw [hka,hkc,mul_div_mul_left _ _ hk]

/-- The possible non-core j-values, Prop. 2.1, printed p. 37. -/
def exceptionalJ (j : ℚ) : Prop :=
  j=2^14*31^3/5^3 ∨ j=2^2*73^3/3^4 ∨ j=1728 ∨ j=0

theorem exceptionalJ_bound {j : ℚ} (h : exceptionalJ j) : hNon j ≤ log 125 := by
  apply log_le_log (by exact_mod_cast j.den_pos : (0:ℝ)<j.den)
  suffices hj : j.den ≤ 125 by exact_mod_cast hj
  rcases h with rfl|rfl|rfl|rfl
  · rw [show (2^14*31^3/5^3:ℚ)=Rat.divInt 488095744 125 by rw [Rat.divInt_eq_div]; norm_num, Rat.den_divInt]
    decide
  · rw [show (2^2*73^3/3^4:ℚ)=Rat.divInt 1556068 81 by rw [Rat.divInt_eq_div]; norm_num, Rat.den_divInt]
    decide
  · decide
  · decide

end
end ExpEstL3
