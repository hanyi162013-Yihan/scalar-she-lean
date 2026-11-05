module

public import SHE.PastTwoChannelAlgebra
public import SHE.NativeHybridInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PastHybridIntegral
open MeasureTheory Set PredictableL2 PastItoInputs PastItoAlgebra
open PredictableItoRotation OrthogonalItoChannels FiniteHaar NativeHybridInput
open scoped NNReal ENNReal
local instance pastHybridIntegral_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance pastHybridIntegral_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance pastHybridIntegral_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance pastHybridIntegral_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

variable [IsProbabilityMeasure μ]
variable {ell₀ M₀ ell M : ℝ} (hell₀ : 0<ell₀) (hM₀ : 0≤M₀)
variable (f₀ : ℝ≥0×Ω→EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell : 0<ell) (hM : 0≤M)
variable (fU fV : ℝ≥0×Ω→EllipticField ell M)
variable (hfU : StronglyMeasurable[𝓕.predictable] fU) (hfV : StronglyMeasurable[𝓕.predictable] fV)
variable (v q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : StoppedFourier.HeatCircle)
variable {Λ θ : ℝ} (hΛ : 0≤Λ) (hθ : |θ|≤1)

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)

/-- Exact post-v hybrid integral decomposition inside the same full-H
integral. The residual channel is literally the right restriction of J. -/
theorem integral_eq :
    J.integral (post 𝓕 μ H v (NativeHybridInput.input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ))=
      J.integral (post 𝓕 μ H v (NativeHybridInput.current 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU hfU q hT x))+
        θ • (rightIntegral 𝓕 μ H J).integral (post 𝓕 μ H v
          (NativeHybridInput.dampedDifference 𝓕 μ H hell hM fU fV hfU hfV q hT x hΛ)) := by
  rw [NativeHybridInput.input,post_add,PastTwoChannelAlgebra.post_rightLift,
    NativeHybridInput.weighted_const_eq,post_smul]
  unfold NativeHybridInput.rightLift
  rw [map_smul,map_add,map_smul]
  rfl

end SHE.PastHybridIntegral
