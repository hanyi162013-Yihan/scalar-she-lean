module

public import SHEStochastic.MatrixHaarNoiseRotation
public import SHEStochastic.MeasurableHilbertSynthesis

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixHaarFrameEnergy
open MeasureTheory MatrixInfiniteHaar
open scoped ENNReal Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalColumn (P : Profile d) (k : d × SHE.FiniteHaar.HaarNode) : Physical (d := d) :=
  factor P (lp.single 2 k 1)

theorem analysis_coordinate (P : Profile d) (u : Physical (d := d)) (k : d × SHE.FiniteHaar.HaarNode) :
    (factor P).adjoint u k=inner ℝ (physicalColumn P k) u :=
  MeasurableHilbertSynthesis.adjoint_coordinate (factor P) u k

theorem summable (P : Profile d) (u : Physical (d := d)) :
    Summable (fun k => ‖inner ℝ (physicalColumn P k) u‖^2) := by
  have hh := (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) ((factor P).adjoint u)).summable
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, analysis_coordinate] using hh

/-- Exact infinite matrix frame energy against every actual vector
spatial test. This is the covariance identity in summable-column form. -/
theorem energy (P : Profile d) (u : Physical (d := d)) :
    (∑' k, ‖inner ℝ (physicalColumn P k) u‖^2)=inner ℝ u (multiplier P u) := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) ((factor P).adjoint u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, analysis_coordinate] at hn
  rw [← hn]
  have hh := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (factor P).adjoint u
  rw [ContinuousLinearMap.adjoint_adjoint, covariance] at hh
  exact hh

theorem pairing (P : Profile d) (u v : Physical (d := d)) :
    (∑' k, inner ℝ (physicalColumn P k) u*inner ℝ (physicalColumn P k) v)=
      inner ℝ u (multiplier P v) := by
  have hh := lp.inner_eq_tsum (𝕜 := ℝ) ((factor P).adjoint u) ((factor P).adjoint v)
  simp only [RCLike.inner_apply, conj_trivial, analysis_coordinate] at hh
  calc
    _ = inner ℝ ((factor P).adjoint u) ((factor P).adjoint v) := by
      rw [hh]
      exact tsum_congr (fun k => mul_comm _ _)
    _ = _ := by
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, covariance]

/-- The actual infinite Haar factor has the same uniform bound as the
square-root covariance factor, by the genuine unitary comparison. -/
theorem factor_bound (P : Profile d) (z : Input (d := d)) :
    ‖factor P z‖ ≤ (NNReal.sqrt P.bound : ℝ)*‖z‖ := by
  have hh := MatrixHaarNoiseRotation.reconstruct P ((MatrixHaarNoiseRotation.rotation P).symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  rw [hh]
  exact (VectorPhysicalFactor.norm_bound (MatrixSqrtReference.field P) _).trans_eq
    (congrArg (fun r : ℝ => (NNReal.sqrt P.bound : ℝ)*r)
      ((MatrixHaarNoiseRotation.rotation P).symm.norm_map z))

end SHEStochastic.MatrixHaarFrameEnergy
