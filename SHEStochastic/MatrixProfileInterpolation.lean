module

public import SHEStochastic.MatrixHaarHigherFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixProfileInterpolation
open MeasureTheory Matrix MatrixInfiniteHaar MatrixPhysicalColumnSmooth
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Convex profile interpolation has fixed ellipticity bounds along
the entire segment; no pointwise positivity neighborhood is assumed. -/
def blend (P Q : Profile d) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Profile d where
  value x := (1-s) • P.value x + s • Q.value x
  measurable := (P.measurable.const_smul (1-s)).add (Q.measurable.const_smul s)
  bound := P.bound + Q.bound
  norm_bound := by
    filter_upwards [P.norm_bound, Q.norm_bound] with x hp hq
    have h1 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
    calc
      _ ≤ ‖(1-s) • P.value x‖ + ‖s • Q.value x‖ := norm_add_le _ _
      _ = (1-s) * ‖P.value x‖ + s * ‖Q.value x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg hs.1]
      _ ≤ (1-s) * (P.bound : ℝ) + s * (Q.bound : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hp h1) (mul_le_mul_of_nonneg_left hq hs.1)
      _ ≤ (P.bound : ℝ) + (Q.bound : ℝ) := by
        nlinarith [mul_nonneg hs.1 P.bound.coe_nonneg, mul_nonneg h1 Q.bound.coe_nonneg]
      _ = _ := rfl
  lower := min P.lower Q.lower
  lower_pos := lt_min P.lower_pos Q.lower_pos
  lower_bound := by
    filter_upwards [P.lower_bound, Q.lower_bound] with x hp hq
    have h1 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
    have hp' : min P.lower Q.lower • (1 : Matrix d d ℝ) ≤ P.value x :=
      (smul_le_smul_of_nonneg_right (min_le_left _ _) zero_le_one).trans hp
    have hq' : min P.lower Q.lower • (1 : Matrix d d ℝ) ≤ Q.value x :=
      (smul_le_smul_of_nonneg_right (min_le_right _ _) zero_le_one).trans hq
    have hh := add_le_add (smul_le_smul_of_nonneg_left hp' h1) (smul_le_smul_of_nonneg_left hq' hs.1)
    simpa only [← add_smul, sub_add_cancel, one_smul] using hh
  upper := max P.upper Q.upper
  upper_pos := P.upper_pos.trans_le (le_max_left _ _)
  upper_bound := by
    filter_upwards [P.upper_bound, Q.upper_bound] with x hp hq
    have h1 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
    have hp' : P.value x ≤ max P.upper Q.upper • (1 : Matrix d d ℝ) :=
      hp.trans (smul_le_smul_of_nonneg_right (le_max_left _ _) zero_le_one)
    have hq' : Q.value x ≤ max P.upper Q.upper • (1 : Matrix d d ℝ) :=
      hq.trans (smul_le_smul_of_nonneg_right (le_max_right _ _) zero_le_one)
    have hh := add_le_add (smul_le_smul_of_nonneg_left hp' h1) (smul_le_smul_of_nonneg_left hq' hs.1)
    simpa only [← add_smul, sub_add_cancel, one_smul] using hh

theorem realize (P Q : Profile d) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    MatrixProfileSymmetry.realize d (blend P Q s hs) =
      (1-s) • MatrixProfileSymmetry.realize d P + s • MatrixProfileSymmetry.realize d Q := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [MatrixProfileHilbert.realize_ae d (blend P Q s hs),
    MatrixProfileHilbert.realize_ae d P, MatrixProfileHilbert.realize_ae d Q,
    Lp.coeFn_add ((1-s) • MatrixProfileHilbert.realize d P) (s • MatrixProfileHilbert.realize d Q),
    Lp.coeFn_smul (1-s) (MatrixProfileHilbert.realize d P),
    Lp.coeFn_smul s (MatrixProfileHilbert.realize d Q)] with x hb hp hq ha hsp hsq
  change MatrixProfileHilbert.realize d (blend P Q s hs) x =
    ((1-s) • MatrixProfileHilbert.realize d P + s • MatrixProfileHilbert.realize d Q) x
  rw [hb, ha]
  simp only [Pi.add_apply]
  rw [hsp, hsq]
  simp only [Pi.smul_apply, hp, hq]
  simp only [blend, map_add, map_smul, Pi.smul_apply]

theorem realize_line (P Q : Profile d) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    MatrixProfileSymmetry.realize d (blend P Q s hs) =
      MatrixProfileSymmetry.realize d P + s •
        (MatrixProfileSymmetry.realize d Q - MatrixProfileSymmetry.realize d P) := by
  rw [realize]
  module

end SHEStochastic.MatrixProfileInterpolation
