module

public import SHEStochastic.BoundedFourierMildRecognition
public import SHEStochastic.SmoothedBoundedHeatInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.BoundedMildAllHeatObservations
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩


/-- Every positive heat scale is allowed. The future heat target T+δ
is not restricted by the integration horizon or by the short-time cap.
The stochastic input is the actual averaged native heat row. -/
theorem observation
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ξ : Ω → RealL2)
    (hMild : BoundedFourierMildRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb J ξ)
    (T δ : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (hδ : 0 < δ) (x : HeatCircle) :
    (fun ω ↦ NativeHeatObservation.functional δ x (W T ω)) =ᵐ[μ]
      fun ω ↦ NativeHeatObservation.functional (T+δ : ℝ≥0) x (ξ ω)+
        J.integral (SmoothedBoundedHeatInput.input F (physical W) (physical_predictable F W hW)
          hG hβ hβ1.le B hb μ H T δ hTH hT hδ x) ω := by
  obtain ⟨Y, hm, he, hs⟩ := hMild
  let U := BoundedHeatCoefficientLift.field (physical W) hG hβ hβ1.le
  let hp := BoundedHeatCoefficientLift.predictable F (physical W) (physical_predictable F W hW) hG hβ hβ1.le
  have hh := HeatRowPhysicalIntegration.integral_ae F U hp
    (BoundedHeatCoefficientLift.projection_holder B) (by norm_num) (by norm_num) μ H
    (Filter.Eventually.of_forall (BoundedHeatCoefficientLift.norm_bound (physical W) hG hβ hβ1.le B hb)) J
    (⟨T, T.property, hT⟩ : HeatParameterPullback.ShortTime) hTH
    (PhysicalHeatKernelMeasure.measure δ hδ x) (fun p ω ↦ Y ω p)
    (fun p ↦ (ContinuousMap.measurable_eval p).comp hm) (fun ω ↦ (Y ω).continuous) he
  change J.integral (SmoothedBoundedHeatInput.input F (physical W) (physical_predictable F W hW)
    hG hβ hβ1.le B hb μ H T δ hTH hT hδ x) =ᵐ[μ]
      (fun ω ↦ ∫ a : HeatCircle, Y ω (HeatParameterPullback.point ⟨T, T.property, hT⟩ a)
        ∂PhysicalHeatKernelMeasure.measure δ hδ x) at hh
  have hd : (0 : ℝ) < δ := by exact_mod_cast hδ
  filter_upwards [hs, hh] with ω hs hh
  have hw := hs T hTH hT
  have ho := congrArg (NativeHeatObservation.functional (δ : ℝ) x) hw
  rw [map_add] at ho
  have hheat := NativeHeatObservation.functional_heat hd T.property x (ξ ω)
  have hrem := NativeRemainderObservation.observation hd x (Y ω)
    (⟨T, T.property, hT⟩ : HeatParameterPullback.ShortTime)
  calc
    NativeHeatObservation.functional (δ : ℝ) x (W T ω) =
        NativeHeatObservation.functional (δ : ℝ) x (NativeHeatObservation.heat T (ξ ω)) +
          NativeHeatObservation.functional (δ : ℝ) x
            (NativeRemainderObservation.remainder (Y ω) ⟨T, T.property, hT⟩) := ho
    _ = NativeHeatObservation.functional ((δ : ℝ)+(T : ℝ)) x (ξ ω) +
        (∫ a : HeatCircle, Y ω (HeatParameterPullback.point ⟨T, T.property, hT⟩ a)
          ∂PhysicalHeatKernelMeasure.measure δ hδ x) := congrArg₂ (· + ·) hheat hrem
    _ = NativeHeatObservation.functional (T+δ : ℝ≥0) x (ξ ω) + _ := by
      have he : (δ : ℝ)+(T : ℝ) = ((T+δ : ℝ≥0) : ℝ) := by
        simp only [NNReal.coe_add, add_comm]
      exact congrArg₂ (· + ·) (congrArg (fun r ↦ NativeHeatObservation.functional r x (ξ ω)) he) hh.symm

end SHEStochastic.BoundedMildAllHeatObservations
