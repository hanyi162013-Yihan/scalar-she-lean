module

public import SHEStochastic.MatrixPhysicalJetBounds
public import SHEStochastic.MatrixEllipticOperatorNorm

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixDirectionBounds
open MeasureTheory MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def localSize (p : List Bool) (v : Domain (d := d)) : ℝ :=
  ‖restricted (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child_measurable p false) v‖+
    ‖restricted (MatrixGlobalHaar.child p true) (MatrixGlobalHaar.child_measurable p true) v‖

theorem localSize_nonneg (p : List Bool) (v : Domain (d := d)) : 0 ≤ localSize p v :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem child_measure (p : List Bool) (b : Bool) :
    (μ).real (MatrixGlobalHaar.child p b)=childLength p :=
  DyadicCellRefinement.measure_real _ _

/-- A single `L²` profile direction has exactly the normalized
cell-average loss, with its actual localized Frobenius norm. -/
theorem normalized_mass (p : List Bool) (b : Bool) (v : Domain (d := d)) :
    MatrixFrobeniusNorm.size (normalizedMass p b v) ≤
      (Real.sqrt (childLength p))⁻¹*
        ‖restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v‖ := by
  have hh := MatrixProfileCellBounds.mass_bound (MatrixGlobalHaar.child p b)
    (MatrixGlobalHaar.child_measurable p b) v.val
  rw [child_measure] at hh
  change MatrixFrobeniusNorm.size ((childLength p)⁻¹ • mass (MatrixGlobalHaar.child p b) v) ≤ _
  rw [MatrixFrobeniusNorm.smul, abs_of_nonneg (inv_nonneg.mpr (childLength_pos p).le)]
  calc
    _ ≤ (childLength p)⁻¹*(Real.sqrt (childLength p)*
        ‖restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v‖) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (childLength_pos p).le)
    _ = _ := by rw [← mul_assoc, mul_comm (childLength p)⁻¹, ← div_eq_mul_inv, Real.sqrt_div_self]

theorem weight_one_input (p : List Bool) (v : Domain (d := d)) :
    MatrixActualCoefficientBounds.weight p v ≤ (Real.sqrt (childLength p))⁻¹*localSize p v := by
  exact (add_le_add (normalized_mass p false v) (normalized_mass p true v)).trans_eq (by unfold localSize; ring)

theorem restriction_bounded (p : List Bool) (b : Bool) (v : Domain (d := d))
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ B) :
    ‖restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) v‖ ≤
      B*Real.sqrt (childLength p) := by
  have hh := MatrixProfileNorms.restriction_bounded (MatrixGlobalHaar.child p b)
    (MatrixGlobalHaar.child_measurable p b) v.val B hB hv
  rwa [child_measure] at hh

theorem normalized_bounded (p : List Bool) (b : Bool) (v : Domain (d := d))
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ B) :
    MatrixFrobeniusNorm.size (normalizedMass p b v) ≤ B := by
  have hh := MatrixProfileCellBounds.mass_bounded (MatrixGlobalHaar.child p b)
    (MatrixGlobalHaar.child_measurable p b) v.val B hB hv
  rw [child_measure] at hh
  change MatrixFrobeniusNorm.size ((childLength p)⁻¹ • mass (MatrixGlobalHaar.child p b) v) ≤ _
  rw [MatrixFrobeniusNorm.smul, abs_of_nonneg (inv_nonneg.mpr (childLength_pos p).le)]
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (childLength_pos p).le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ (childLength_pos p).ne', one_mul])

theorem weight_bounded (p : List Bool) (v : Domain (d := d))
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ B) :
    MatrixActualCoefficientBounds.weight p v ≤ 2*B := by
  have hh := add_le_add (normalized_bounded p false v B hB hv) (normalized_bounded p true v B hB hv)
  change MatrixFrobeniusNorm.size (normalizedMass p false v)+
    MatrixFrobeniusNorm.size (normalizedMass p true v) ≤ 2*B
  convert! hh using 1 <;> ring

def profileBound (P : Profile d) : ℝ := ‖MatrixProfileHilbert.toVector d‖*P.upper

theorem profile_bound (P : Profile d) :
    ∀ᵐ x ∂μ, ‖(MatrixProfileSymmetry.realize d P).val x‖ ≤ profileBound P := by
  filter_upwards [MatrixProfileHilbert.realize_ae d P, P.lower_bound, P.upper_bound] with x hx hLo hHi
  have hb := MatrixEllipticOperatorNorm.upper (P.value x)
    (le_trans (smul_nonneg P.lower_pos.le zero_le_one) hLo) P.upper P.upper_pos.le hHi
  change ‖MatrixProfileHilbert.realize d P x‖ ≤ _
  rw [hx]
  exact ((MatrixProfileHilbert.toVector d).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

end SHEStochastic.MatrixDirectionBounds
