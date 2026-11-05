module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SymmetricBilinearUnitBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true norm of a real symmetric bilinear form is controlled by
its diagonal on the unit sphere. Normalization and polarization retain
the constant, without dimension-dependent coordinate expansion. -/
theorem norm_le (B : E →L[ℝ] E →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ x y, B x y = B y x)
    (hd : ∀ x, ‖x‖ = 1 → |B x x| ≤ C) : ‖B‖ ≤ C := by
  have hdiag (x : E) : |B x x| ≤ C*‖x‖^2 := by
    by_cases hx : x = 0
    · simp [hx]
    let u := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hx]
    have he : x = ‖x‖ • u := by simp [u, smul_smul, hx]
    have hval : B x x = ‖x‖^2*B u u := by
      calc
        _ = B (‖x‖ • u) (‖x‖ • u) := congrArg₂ (fun v w => B v w) he he
        _ = _ := by simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    rw [hval, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hd u hu) (sq_nonneg _)).trans_eq (mul_comm _ _)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro x hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro y hy
  have hp : B (x+y) (x+y)-B (x-y) (x-y) = 4*B x y := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    rw [hs y x]
    ring
  have hh := abs_sub (B (x+y) (x+y)) (B (x-y) (x-y))
  rw [hp, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hh
  have hb := add_le_add (hdiag (x+y)) (hdiag (x-y))
  rw [← mul_add, parallelogram_law_with_norm ℝ x y, hx, hy] at hb
  rw [Real.norm_eq_abs]
  nlinarith only [hh, hb]

end SHEStochastic.SymmetricBilinearUnitBound
