module
public import SHE.TwoChannelCutoffModel

public import SHE.MixedNativeJointPastIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeOrdinaryModel
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianItoTest GaussianTaylor GaussianTaylorAverage CovarianceEndpoint
open scoped NNReal ENNReal
local instance mixedNativeOrdinaryModel_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeOrdinaryModel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeOrdinaryModel_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeOrdinaryModel_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeOrdinaryModel_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeOrdinaryModel_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

theorem cancellation {n : ℕ} (W : EndpointWindow n) (F : State n→ℝ)
    (Γ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (z : State n) :
    backwardDerivative W F t z+(1/2:ℝ)*covarianceAction Γ (hessian (backward W F t) z)=
      (1/2:ℝ)*covarianceAction (Γ-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
        (hessian (backward W F t) z) := by
  rw [NativeControlledGenerator.covarianceAction_sub]
  unfold backwardDerivative
  ring

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

/-- The actual first member is an ordinary two-channel solution with
rough coefficient aU and the original separate noise integrals. -/
def model (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J):
    TwoChannelCutoffModel.Model 𝓕 μ H κ aU ell M where
  additive_pos:=hκ
  lower_pos:=hell
  variance_measurable:=haU
  variance_bounds:=hbU
  coefficient:=ContinuousHeatMild.coefficientFunction haU hell hbU S.first
  coefficient_predictable:=S.first_coefficient
  state:=Function.uncurry S.first
  state_predictable:=S.first_predictable
  state_continuous:=S.first_continuous
  null_complete:=hnull
  additiveIto:=I₀
  residualIto:=I₁
  scalarIto:=J
  additive_naturality:=hIJ₀
  residual_naturality:=hIJ₁
  finiteIto:=hJ
  initial:=u₀
  additiveInput:=S.additiveInput
  residualInput:=S.residualInput
  additive_kernel:=S.additive_kernel
  residual_kernel:=S.residual_kernel
  mild_identity:=S.first_mild
  coefficient_identity:=fun _=>rfl

end SHE.MixedNativeOrdinaryModel
