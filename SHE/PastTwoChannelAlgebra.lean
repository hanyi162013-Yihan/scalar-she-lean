module

public import SHE.PastItoAlgebra
public import SHE.NativeHybridInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PastTwoChannelAlgebra
open MeasureTheory Set PredictableL2 PastItoInputs PastItoAlgebra
open PredictableItoRotation OrthogonalItoChannels FiniteHaar NativeHybridInput
open scoped NNReal ENNReal
local instance pastTwoChannelAlgebra_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance pastTwoChannelAlgebra_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance pastTwoChannelAlgebra_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance pastTwoChannelAlgebra_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

theorem post_block (v : ℝ≥0) (u w : Process (E := RealHaarInput) 𝓕 μ H) :
    post 𝓕 μ H v (TwoChannelItoRows.block 𝓕 μ H u w)=
      TwoChannelItoRows.block 𝓕 μ H (post 𝓕 μ H v u) (post 𝓕 μ H v w) := by
  rw [TwoChannelItoRows.block,post_add,post_isometry,post_isometry]
  rfl

variable [IsProbabilityMeasure μ]

theorem post_rightLift (v : ℝ≥0) (u : Process (E := RealHaarInput) 𝓕 μ H) :
    post 𝓕 μ H v (rightLift 𝓕 μ H u)=rightLift 𝓕 μ H (post 𝓕 μ H v u) :=
  post_isometry 𝓕 μ H (fun _ => right (C := RealHaarInput)) (right_measurable 𝓕) v u

variable {ell₀ M₀ ell M : ℝ} (hell₀ : 0<ell₀) (hM₀ : 0≤M₀)
variable (f₀ : ℝ≥0×Ω→EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell : 0<ell) (hM : 0≤M)
variable (fU fV : ℝ≥0×Ω→EllipticField ell M)
variable (hfU : StronglyMeasurable[𝓕.predictable] fU) (hfV : StronglyMeasurable[𝓕.predictable] fV)
variable (v q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : StoppedFourier.HeatCircle)
variable {Λ θ : ℝ} (hΛ : 0≤Λ) (hθ : |θ|≤1)

/-- Exact post-v decomposition of the same full-H hybrid input. The
additive channel stays common, while only the residual difference is
damped. No fresh or independently restarted stochastic integral appears. -/
theorem post_hybrid_eq :
    post 𝓕 μ H v (input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ)=
      TwoChannelItoRows.block 𝓕 μ H
        (post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell₀ hM₀ f₀ hf₀ hT x))
        (post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM fU hfU hT x))+
      rightLift 𝓕 μ H (PredictableContraction.weighted 𝓕 μ H (fun _ => θ) stronglyMeasurable_const (fun _ => hθ)
        (PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ q)
          (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q)
          (post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM fV hfV hT x)-
            post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM fU hfU hT x)))) := by
  unfold input current dampedDifference
  rw [post_add,post_block,post_rightLift,post_weighted,post_weighted,post_sub]

end SHE.PastTwoChannelAlgebra
