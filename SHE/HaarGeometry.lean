module

public import SHE.HaarHigherColumns

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat
local instance haarGeometry_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem fourier_sub_one_sq_norm (n : ℤ) (x : AddCircle (1 : ℝ)) :
    ‖fourier n x - 1‖ ^ 2 ≤ (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  induction x using Quotient.inductionOn with
  | _ r =>
    have hi : (((round r : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨round r, by simp only [zsmul_eq_mul, mul_one]⟩
    have he : (((r - (round r : ℝ)) : ℝ) : AddCircle (1 : ℝ)) = (r : AddCircle (1 : ℝ)) := by
      rw [QuotientAddGroup.mk_sub, hi, sub_zero]
    have hb := CircleFractional.unitAmplitude_le_quadratic ((n : ℝ) * (r - (round r : ℝ)))
    rw [← CircleFractional.frequencyAmplitude_scale] at hb
    change ‖fourier n ((r - (round r : ℝ) : ℝ) : AddCircle (1 : ℝ)) - 1‖ ^ 2 ≤ _ at hb
    rw [he] at hb
    rw [AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one, sq_abs]
    exact hb.trans_eq (by ring)

theorem fourier_lipschitz_bound (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    ‖fourier n x - fourier n y‖ ≤ 2 * Real.pi * |(n : ℝ)| * dist x y := by
  have he : fourier n x - fourier n y = fourier n y * (fourier n (x-y) - 1) := by
    rw [mul_sub, mul_one, ← CircleFractional.fourier_translate]
    rw [show y + (x-y) = x by abel]
  rw [he, norm_mul, show ‖fourier n y‖ = 1 from Circle.norm_coe _, one_mul]
  have hb := fourier_sub_one_sq_norm n (x-y)
  rw [dist_eq_norm]
  have hp : 0 ≤ 2 * Real.pi * |(n : ℝ)| * ‖x-y‖ := by positivity
  have hs : (2 * Real.pi * |(n : ℝ)| * ‖x-y‖) ^ 2 =
      (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 * ‖x-y‖ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  nlinarith [sq_nonneg (‖fourier n (x-y) - 1‖ - 2 * Real.pi * |(n : ℝ)| * ‖x-y‖)]

theorem bottomLeaf_ordinal_adjacent (p : List Bool) :
    gridOrdinal (p.length+1) (bottomLeaf p true) = gridOrdinal (p.length+1) (bottomLeaf p false) + 1 := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b
    · exact ih
    · change 2 ^ (p.length+1) + gridOrdinal (p.length+1) (bottomLeaf p true) =
        (2 ^ (p.length+1) + gridOrdinal (p.length+1) (bottomLeaf p false)) + 1
      omega

def nodeCenter (p : List Bool) : AddCircle (1 : ℝ) :=
  DyadicApproximation.cellLeft (p.length+1) (gridCellEquiv (p.length+1) (bottomLeaf p false))

def nodeLength (p : List Bool) : ℝ := 2 / (((2 ^ (p.length+1) : ℕ) : ℝ))

theorem nodeLength_pos (p : List Bool) : 0 < nodeLength p := by unfold nodeLength; positivity

theorem childCenter_distance (p : List Bool) :
    dist (DyadicApproximation.cellLeft (p.length+1) (gridCellEquiv (p.length+1) (bottomLeaf p true)))
      (nodeCenter p) ≤ (((2 ^ (p.length+1) : ℕ) : ℝ))⁻¹ := by
  unfold nodeCenter DyadicApproximation.cellLeft
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans_eq
  rw [gridCellEquiv_val, gridCellEquiv_val, bottomLeaf_ordinal_adjacent]
  push_cast
  have hs : (((2 ^ (p.length+1) : ℕ) : ℝ)) ≠ 0 := by positivity
  have he : ((gridOrdinal (p.length+1) (bottomLeaf p false) : ℝ) + 1) /
      (((2 ^ (p.length+1) : ℕ) : ℝ)) - (gridOrdinal (p.length+1) (bottomLeaf p false) : ℝ) /
      (((2 ^ (p.length+1) : ℕ) : ℝ)) = (((2 ^ (p.length+1) : ℕ) : ℝ))⁻¹ := by field_simp; ring
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at he
  rw [he, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Every literal periodic node lies in the ball of its actual interval
length about its left endpoint, including the circle identification. -/
theorem nodeCell_distance (p : List Bool) (y : AddCircle (1 : ℝ)) (hy : y ∈ nodeCell p) :
    dist y (nodeCenter p) ≤ nodeLength p := by
  rcases hy with hy | hy
  · have hh := DyadicApproximation.cellLeft_distance (p.length+1) y
    rw [show cellIndex (p.length+1) y = gridCellEquiv (p.length+1) (bottomLeaf p false) from hy] at hh
    exact hh.trans (by unfold nodeLength; rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity))
  · have hh := DyadicApproximation.cellLeft_distance (p.length+1) y
    rw [show cellIndex (p.length+1) y = gridCellEquiv (p.length+1) (bottomLeaf p true) from hy] at hh
    exact (dist_triangle _ _ _).trans ((add_le_add hh (childCenter_distance p)).trans_eq (by
      unfold nodeLength
      ring))

end SHE.FiniteHaar
