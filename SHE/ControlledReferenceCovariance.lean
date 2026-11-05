module

public import SHE.ControlledReferenceWindows
public import SHE.CovarianceCoefficientContinuity
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceCovariance
open Set MeasureTheory StoppedFourier ControlledProfile ControlledReferenceWindows
open WordRecursion CovarianceMatrix GaussianContinuity GaussianItoTest
local instance controlledReferenceCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open scoped Matrix.Norms.Elementwise
variable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0≤Λ) (θ v : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable {n : ℕ} (Z : Fin n→Observation) (b : ℝ) {q : ℝ} (hqb : q≤b)
variable (htarget : ∀ i,b≤(Z i).target)

include hΛ hsmall hqb htarget in
theorem covariance_inputs_continuous :
    Continuous (fun p : Inputs => covariance (coefficient P Λ θ v p) Z q b) :=
  CovarianceCoefficientContinuity.continuous_covariance (coefficient P Λ θ v)
    (coefficient_section_measurable P Λ θ v)
    (coefficient_inputs_continuous P Λ θ v hΛ hsmall) Z P.upper_nonneg hqb htarget
    (fun p t _ x => coefficient_abs_bound P Λ θ v p (t,x))

variable (hvb : v≤b)

include hΛ hsmall in
theorem path_inputs_continuous (t : ℝ) :
    Continuous (fun p : Inputs => (window P Λ θ v Z b hvb htarget p).path t) := by
  apply Continuous.subtype_mk
  have hh := covariance_inputs_continuous P hΛ θ v hsmall Z b
    (ClippedCovariance.clip_mem hvb t).2 htarget
  exact hh

include hΛ hsmall in
/-- The actual backward Gaussian smoothing and its Hessian are
continuous in both original random-past state parameters, with singular
covariance matrices allowed. -/
theorem backward_inputs_continuous {F : WordRecursion.State n→ℝ} (hF : SmoothCylinders.BoundedSmooth F) (t : ℝ) :
    Continuous (fun p : Inputs×WordRecursion.State n => backward (window P Λ θ v Z b hvb htarget p.1) F t p.2) := by
  obtain ⟨M,hM⟩ := hF.norm_bound
  exact CovarianceContinuity.continuous_gaussian_average_comp
    (fun p : Inputs×WordRecursion.State n => ((window P Λ θ v Z b hvb htarget p.1).path t).val)
    ((path_inputs_continuous P hΛ θ v hsmall Z b htarget hvb t).subtype_val.comp continuous_fst)
    (fun p => ((window P Λ θ v Z b hvb htarget p.1).path t).property)
    Prod.snd continuous_snd F hF.smooth.continuous hM

include hΛ hsmall in
theorem hessian_inputs_continuous {F : WordRecursion.State n→ℝ} (hF : SmoothCylinders.BoundedSmooth F) (t : ℝ) :
    Continuous (fun p : Inputs×WordRecursion.State n => GaussianTaylor.hessian
      (backward (window P Λ θ v Z b hvb htarget p.1) F t) p.2) := by
  have hFs : UniformSmooth.UniformBoundedSmooth (fun _ : Inputs => F) :=
    UniformSmooth.UniformBoundedSmooth.fixed hF
  exact GaussianParameterContinuity.continuous_average_hessian (fun _ : Inputs => F)
    (hF.smooth.continuous.comp continuous_snd) hFs
    (fun p => (window P Λ θ v Z b hvb htarget p).path t)
    (path_inputs_continuous P hΛ θ v hsmall Z b htarget hvb t)

end SHE.ControlledReferenceCovariance
