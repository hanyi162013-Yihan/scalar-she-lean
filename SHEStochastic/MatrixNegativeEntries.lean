module

public import SHEStochastic.MatrixCellEntries
public import SHEStochastic.MatrixDirectionBounds
public import SHEStochastic.MatrixTransformedJets
public import SHE.HaarNegativeColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixNegativeEntries
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def operator (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) : RealL2 →L[ℝ] CircleHeat.CircleL2 :=
  ((besselHalf Λ ρ hΛ hρ).restrictScalars ℝ).comp realEmbed
def scaled (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (n : ℕ) : RealL2 →L[ℝ] CircleHeat.CircleL2 :=
  scale Λ ρ n • operator Λ ρ hΛ hρ

def localNorm (p : List Bool) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : Domain (d := d)) : ℝ :=
  MatrixTransformedJets.localSize p false (operator Λ ρ hΛ hρ) v +
    MatrixTransformedJets.localSize p true (operator Λ ρ hΛ hρ) v

theorem localNorm_nonneg (p : List Bool) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : Domain (d := d)) :
    0 ≤ localNorm p Λ ρ hΛ hρ v :=
  add_nonneg (transformedSize_nonneg _ _) (transformedSize_nonneg _ _)

theorem scale_positive (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (n : ℕ) : 0 < scale Λ ρ n := by
  have hΛ0 := zero_lt_one.trans_le hΛ
  unfold scale
  positivity

theorem size_scaled (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (n : ℕ) (v : MatrixProfileHilbert.Space d) :
    transformedSize (scaled Λ ρ hΛ hρ n) v = scale Λ ρ n * transformedSize (operator Λ ρ hΛ hρ) v := by
  simp only [transformedSize, scaled, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (scale_positive Λ ρ hΛ n), Finset.mul_sum]

theorem sqrt_child_inverse (p : List Bool) :
    (Real.sqrt (childLength p))⁻¹ = Real.sqrt (((2 ^ (p.length+1) : ℕ) : ℝ)) := by
  rw [childLength, Real.sqrt_inv, inv_inv]

/-- Negative control of each actual normalized matrix mass is obtained
by applying the existing scalar inverse estimate to every signed entry. -/
theorem normalized_mass {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (b : Bool) (v : Domain (d := d)) :
    MatrixFrobeniusNorm.size (normalizedMass p b v) ≤
      Real.sqrt (CircleHeat.inverseConstant 1 ρ) * (Real.sqrt (childLength p))⁻¹ * scale Λ ρ (p.length+1) *
        MatrixTransformedJets.localSize p b (operator Λ ρ hΛ hρ.le) v := by
  apply (MatrixCellEntries.size_le_sum_abs _).trans
  unfold MatrixTransformedJets.localSize transformedSize
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro j hj
  rw [MatrixCellEntries.normalized_entry, sqrt_child_inverse]
  have hh := CellNegative.localAverage_negative_bound hΛ hρ hρhalf (p.length+1) (bottomLeaf p b) (realEmbed (entry r j v.val))
  rw [← MatrixCellEntries.restricted_entry] at hh
  exact hh

theorem mass_weight {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (p : List Bool) (v : Domain (d := d)) :
    MatrixActualCoefficientBounds.weight p v ≤
      (Real.sqrt (childLength p))⁻¹ *
        (negativeSlotConstant ρ * scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v) := by
  have hh := add_le_add (normalized_mass hΛ hρ hρhalf p false v) (normalized_mass hΛ hρ hρhalf p true v)
  apply hh.trans
  have hc : Real.sqrt (CircleHeat.inverseConstant 1 ρ) ≤ negativeSlotConstant ρ := le_max_left _ _
  have he : Real.sqrt (CircleHeat.inverseConstant 1 ρ) * (Real.sqrt (childLength p))⁻¹ * scale Λ ρ (p.length+1) *
      MatrixTransformedJets.localSize p false (operator Λ ρ hΛ hρ.le) v +
    Real.sqrt (CircleHeat.inverseConstant 1 ρ) * (Real.sqrt (childLength p))⁻¹ * scale Λ ρ (p.length+1) *
      MatrixTransformedJets.localSize p true (operator Λ ρ hΛ hρ.le) v =
      Real.sqrt (CircleHeat.inverseConstant 1 ρ) *
        ((Real.sqrt (childLength p))⁻¹ * scale Λ ρ (p.length+1) * localNorm p Λ ρ hΛ hρ.le v) := by
    unfold localNorm
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg (by positivity) (scale_positive Λ ρ hΛ _).le)
    (localNorm_nonneg p Λ ρ hΛ hρ.le v))).trans_eq (by ring)

end SHEStochastic.MatrixNegativeEntries
