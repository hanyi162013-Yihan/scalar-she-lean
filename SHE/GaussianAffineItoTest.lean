module

public import SHE.GaussianAffineTimeRegularity
public import SHE.GaussianAffineEnvelope
public import SHE.LocalizedItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.GaussianAffineFields
open MeasureTheory Set SmoothCylinders GaussianIncrement
open scoped NNReal ENNReal
variable {k n : ℕ}

/-- Actual Gaussian reserves with a moving affine mean satisfy the
localized Itô test conditions. All analytic hypotheses here concern
the displayed affine coefficients; no enlarged Itô formula is used. -/
theorem smoothTimeTest (W : ClippedCovariance.ObservationWindow n)
    {F : State n→ℝ} (hF : BoundedSmooth F)
    (L dL : ℝ→State k→L[ℝ]State n) (m dm : ℝ→State n)
    {K D : ℝ} (hK : 0≤K) (hLbound : ∀ t,‖L t‖≤K) (hD : 0≤D)
    (KL Km : ℝ≥0) (hLlip : LipschitzWith KL L) (hmlip : LipschitzWith Km m)
    (hdL : Measurable dL) (hdm : Measurable dm)
    (hLderiv : ∀ᵐ t : ℝ,t∈Ioo W.left W.right → HasDerivAt L (dL t) t)
    (hmderiv : ∀ᵐ t : ℝ,t∈Ioo W.left W.right → HasDerivAt m (dm t) t)
    (hdLbound : ∀ t∈Ioo W.left W.right,‖dL t‖≤D)
    (hdmbound : ∀ t∈Ioo W.left W.right,‖dm t‖≤D) :
    LocalizedItoTest.SmoothTimeTest W.left W.right
      (value W.path F L m) (derivative W F L dL m dm) := by
  refine ⟨continuous_value W.continuous_path hF hLlip.continuous hmlip.continuous,
    uniform_smooth W.path hF L m hK hLbound,
    time_absolutelyContinuous W hF L m KL Km hLlip hmlip,
    ae_time_derivative W hF L dL m dm hLderiv hmderiv,
    derivative_measurable W hF hLlip.continuous hmlip.continuous hdL hdm,
    derivative_state_continuous W hF L dL m dm,?_⟩
  obtain ⟨V,hV,hbound⟩ := derivative_linear_envelope W hF L dL m dm hD hdLbound hdmbound
  exact ⟨fun _ => V,intervalIntegrable_const,fun t ht => ⟨hV,hbound t ht⟩⟩

end SHE.GaussianAffineFields
