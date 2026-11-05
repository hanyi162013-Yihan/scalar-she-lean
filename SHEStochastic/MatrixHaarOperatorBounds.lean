module

public import SHEStochastic.MatrixHaarFrameEnergy
public import SHEStochastic.FiniteSynthesisNorm

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixHaarOperatorBounds
open MatrixInfiniteHaar
open scoped Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem synthesis_norm (P : Profile d) : ‖synthesis P‖ ≤ Real.sqrt P.lower⁻¹ :=
  FiniteSynthesisNorm.bound (column P) P.lower⁻¹ (inv_nonneg.mpr P.lower_pos.le)
    (WeightedRieszSynthesis.finite_upper (column P) (multiplier P) (gram P) P.lower P.lower_pos (coercive P))

/-- The actual inverse has the ellipticity bound asserted for the
manuscript's infinite matrix Haar factor. -/
theorem inverse_norm (P : Profile d) :
    ‖(equivalence P).symm.toContinuousLinearMap‖ ≤ Real.sqrt P.lower⁻¹ := by
  change ‖(synthesis P).adjoint‖ ≤ _
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact synthesis_norm P

theorem sqrt_bound (P : Profile d) (u : Physical (d := d)) :
    ‖MatrixSqrtReference.operator P u‖ ≤ Real.sqrt P.upper*‖u‖ := by
  have hh := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (MatrixSqrtReference.operator P) u
  rw [MatrixSqrtReference.selfadjoint, MatrixSqrtReference.square] at hh
  have hb := bounded P u
  change inner ℝ u (multiplier P u) ≤ _ at hb
  have he : ‖MatrixSqrtReference.operator P u‖^2 ≤ P.upper*‖u‖^2 := by rw [hh]; exact hb
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt P.upper_pos.le]

theorem factor_bound (P : Profile d) (z : Input (d := d)) :
    ‖factor P z‖ ≤ Real.sqrt P.upper*‖z‖ := by
  let J := MatrixHaarNoiseRotation.rotation P
  have hh := MatrixHaarNoiseRotation.reconstruct P (J.symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  rw [hh]
  change ‖MatrixSqrtReference.operator P (VectorWhiteCoordinates.analysis.symm (J.symm z))‖ ≤ _
  exact (sqrt_bound P _).trans_eq (by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map])

theorem factor_norm (P : Profile d) : ‖factor P‖ ≤ Real.sqrt P.upper :=
  (factor P).opNorm_le_bound (Real.sqrt_nonneg _) (factor_bound P)

end SHEStochastic.MatrixHaarOperatorBounds
