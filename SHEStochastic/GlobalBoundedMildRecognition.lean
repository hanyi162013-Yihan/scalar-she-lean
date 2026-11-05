module

public import SHEStochastic.GlobalBoundedHeatLocalization
public import SHEStochastic.UnboundedGlobalMildRecognition
public import SHEStochastic.GlobalHeatPathTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalBoundedMildRecognition
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open HeatParameterCover HeatParameterCoordinates StoppedPathPasting UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))

/-- A continuous version of the uniformly bounded convolution is the
actual weak solution's mild remainder on one closed-horizon event.
This reuses local recognition and its continuous-path closure. -/
theorem closed (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (Y : Ω → C(Parameter, ℝ)) (hY : Measurable Y)
    (hrep : ∀ p, (fun sample ↦ Y sample p) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (GlobalBoundedHeatCoefficientLift.input F (physical W) (physical_predictable F W hW)
          hG hβ hβ1.le B hb μ H (GlobalHeatParameter.time H p) (GlobalHeatParameter.time_le_horizon H p) (center p))) :
    ∀ᵐ sample ∂μ, ∀ (T : ℝ≥0) (hTH : T≤H),
      W T sample = NativeHeatObservation.heat T (ξ sample) +
        NativeRemainderObservation.remainder (Y sample) (GlobalHeatRowPhysicalIntegration.unitTime H hH T hTH) := by
  apply UnboundedGlobalMildRecognition.close_representation μ H W ξ hH hcW
    (fun p sample ↦ Y sample p) (fun sample ↦ (Y sample).continuous)
  apply UnboundedGlobalMildRecognition.fixed_of_local F μ H W hW hG hβ hβ1 P e ξ hH hcW hEquation
    (fun p sample ↦ Y sample p) (fun p ↦ (ContinuousMap.measurable_eval p).comp hY)
    (fun sample ↦ (Y sample).continuous)
  intro N p
  have he := GlobalBoundedHeatLocalization.integral_agrees F (physical W) (physical_predictable F W hW)
    hG hβ hβ1 B hb μ H (physical_continuous W hcW) N (GlobalHeatParameter.time H p)
    (GlobalHeatParameter.time_le_horizon H p) (center p) P e hnull
  filter_upwards [hrep p, he] with sample hp he hbefore
  exact hp.trans (he hbefore.le).symm

theorem path_eq (ξ : Ω → RealL2) (hH : 0 < H)
    (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (Y : Ω → C(Parameter, ℝ)) (hY : Measurable Y)
    (hrep : ∀ p, (fun sample ↦ Y sample p) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (GlobalBoundedHeatCoefficientLift.input F (physical W) (physical_predictable F W hW)
          hG hβ hβ1.le B hb μ H (GlobalHeatParameter.time H p) (GlobalHeatParameter.time_le_horizon H p) (center p))) :
    NativeContinuousPath.path H W hcW =ᵐ[μ]
      fun sample ↦ GlobalHeatPathTightness.path H hH
        (ξ sample) (Y sample) := by
  filter_upwards [closed F μ H W hW hG hβ hβ1 B hb P e ξ hH hcW hnull hEquation Y hY hrep]
    with sample hs
  apply ContinuousMap.ext
  intro t
  have ht0 : (0 : ℝ) ≤ t.val := t.property.1
  have htH : t.val.toNNReal≤H := Real.toNNReal_le_iff_le_coe.mpr t.property.2
  have hh := hs t.val.toNNReal htH
  convert hh using 1 <;> simp only [NativeContinuousPath.path,GlobalHeatPathTightness.path,
    MildPathTightness.path,ContinuousMap.coe_mk,GlobalHeatPathTightness.timeMap,
    GlobalHeatRowPhysicalIntegration.unitTime,GlobalHeatParameter.normalized,Real.coe_toNNReal _ ht0]

end SHEStochastic.GlobalBoundedMildRecognition
