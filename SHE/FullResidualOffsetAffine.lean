module

public import SHE.FullResidualAssignedAverage
public import SHE.NormalizedLeafOffsets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.OffsetAssignedLeafMoments
open Set MeasureTheory Real GaussianAssignmentBlocks
variable {r k : ℕ}

/-- Only unassigned original leaves depend on the current offset
budget, and that dependence is exactly affine. -/
theorem leafConstant_affine (P : CanonicalCovariance.ProfileParameters) (p : ℕ) (C0 : ℝ)
    (choices : List (Fin r×Fin k)) (factor : Fin k) :
    leafConstant P p C0 choices factor=leafConstant P p 0 choices factor+
      (if block choices factor=[] then (2:ℝ)^(2*p-1) else 0)*C0 := by
  classical
  unfold leafConstant
  split_ifs <;> ring

end SHE.OffsetAssignedLeafMoments

namespace SHE.FullResidualAssignedMoments
open Set MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {r m : ℕ}

def offsetSlope (b : ℕ) (choices : List (Fin r×Fin (m+1))) : ℝ :=
  ∑ j : Fin m,if block choices j.succ=[] then (2:ℝ)^(2*(b*(m+2))-1) else 0

theorem offsetSlope_nonneg (b : ℕ) (choices : List (Fin r×Fin (m+1))) : 0≤offsetSlope b choices := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- The complete score/root/rough word constant is affine in the
normalized current offset budget. No product of uncontrolled stochastic
offset moments is introduced when Gaussian covariances vary with the past. -/
theorem constant_affine (P : CanonicalCovariance.ProfileParameters) (b : ℕ)
    (choices : List (Fin r×Fin (m+1))) (C0 : ℝ) :
    constant P r m choices b C0=constant P r m choices b 0+offsetSlope b choices*C0 := by
  unfold constant offsetSlope
  simp_rw [OffsetAssignedLeafMoments.leafConstant_affine P (b*(m+2)) C0]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  ring

theorem constant_budget_integrable (μ : Measure Ω) (P : CanonicalCovariance.ProfileParameters)
    (b : ℕ) (choices : List (Fin r×Fin (m+1))) (C0 : Ω→ℝ) (hi : Integrable C0 μ) [IsFiniteMeasure μ] :
    Integrable (fun ω=>constant P r m choices b (C0 ω)) μ := by
  have he : (fun ω=>constant P r m choices b (C0 ω)) =
      (fun ω=>constant P r m choices b 0+offsetSlope b choices*C0 ω) :=
    funext (fun ω=>constant_affine P b choices (C0 ω))
  rw [he]
  exact (integrable_const _).add (hi.const_mul _)

/-- Conditional event offset bounds transfer linearly to the true
varying-data Gaussian word constant, preserving the exact event mass. -/
theorem integral_constant_budget_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (b : ℕ) (choices : List (Fin r×Fin (m+1)))
    (C0 : Ω→ℝ) (hi : Integrable C0 μ) (Cbar : ℝ)
    (hb : (∫ ω,C0 ω ∂μ)≤Cbar*μ.real Set.univ) :
    (∫ ω,constant P r m choices b (C0 ω) ∂μ)≤constant P r m choices b Cbar*μ.real Set.univ := by
  have he : (fun ω=>constant P r m choices b (C0 ω)) =
      (fun ω=>constant P r m choices b 0+offsetSlope b choices*C0 ω) :=
    funext (fun ω=>constant_affine P b choices (C0 ω))
  rw [he,constant_affine P b choices Cbar]
  rw [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,integral_const]
  simp only [smul_eq_mul]
  have hh := add_le_add_left (mul_le_mul_of_nonneg_left hb (offsetSlope_nonneg b choices))
    (μ.real Set.univ*constant P r m choices b 0)
  convert! hh using 1 <;> ring

end SHE.FullResidualAssignedMoments
