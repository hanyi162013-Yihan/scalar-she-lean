module
public import SHE.PredictableScalarHaarRows
public import SHE.HeatObservationUniqueness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.OriginalNativeHeatEquation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2
open OrthogonalItoChannels StoppedFourier NativeHeatObservation
open scoped NNReal ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (D : SmoothApproximation.ScalarData)
variable (B : StandardTerminalIto (C:=Both RealL2) (E:=ℝ) 𝓕 μ H) (u₀ : RealL2)

/-- The original one-noise heat equation, tested against every positive
heat observation. The second physical noise coordinate of every input
is exactly zero by originalRow_ae. On an ordinary independent-noise
enlargement this is the original g(U) mild equation, before splitting. -/
def Equation (U : ℝ≥0 → Ω → RealL2)
    (hU : StronglyMeasurable[𝓕.predictable] (Function.uncurry U)) : Prop :=
  ∀(q : ℝ≥0), q ≤ H → ∀(ε : ℝ)(hε : 0 < ε)(x : HeatCircle),
    (fun ω => functional ε x (U q ω)) =ᵐ[μ]
      (fun ω => functional ((q:ℝ)+ε) x u₀ + B.integral
        (PredictableScalarHaarRotation.originalRow 𝓕 μ H D (Function.uncurry U) hU
          (T:=(q:ℝ)+ε) (t:=(q:ℝ)) (by linarith) x) ω)

structure Data where
  value : ℝ≥0 → Ω → RealL2
  continuous : ∀ω, Continuous (fun t => value t ω)
  predictable : StronglyMeasurable[𝓕.predictable] (Function.uncurry value)
  equation : Equation 𝓕 μ H D B u₀ value predictable

end SHE.OriginalNativeHeatEquation
