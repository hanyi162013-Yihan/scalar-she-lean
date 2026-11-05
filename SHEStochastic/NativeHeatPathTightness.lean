module

public import SHEStochastic.NativeRemainderObservation
public import SHEStochastic.BoundedHeatTightness
public import SHEStochastic.StoppedPathPasting
public import SHEStochastic.MildPathTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeHeatPathTightness
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open HeatParameterCover HeatParameterPullback StoppedPathPasting
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

def timeMap (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) : C(Time H, ShortTime) :=
  ⟨fun t ↦ ⟨t.val, t.property.1, t.property.2.trans hH⟩, continuous_subtype_val.subtype_mk _⟩

/-- The original native L2 state path, obtained from a continuous
physical remainder and the deterministic heat flow of L2 initial data. -/
def path (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (u₀ : RealL2) (Y : C(Parameter, ℝ)) : Path H RealL2 :=
  ⟨fun t ↦ NativeHeatObservation.heat t.val u₀ + NativeRemainderObservation.remainder Y (timeMap H hH t),
    (RealHeat.continuous_realHeat_action.comp
      ((continuous_subtype_val.div_const NativeHeatObservation.timeScale).prodMk continuous_const)).add
        ((NativeRemainderObservation.continuous_remainder Y).comp (timeMap H hH).continuous)⟩

/-- Passing from the compact parameter field to the actual state path
is a contraction. No extra regularity of the initial L2 data is needed. -/
theorem lipschitz (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (u₀ : RealL2) :
    LipschitzWith 1 (path H hH u₀) :=
  MildPathTightness.lipschitz H (timeMap H hH) u₀

/-- Uniform tightness of the native convolution fields transfers to
the complete mild state paths by the same proved contraction. -/
theorem tight {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → C(Parameter, ℝ)) (hY : ∀ k, Measurable (Y k))
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (Y k))))
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (u₀ : RealL2) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ path H hH u₀ (Y k sample)))) :=
  MildPathTightness.tight μ Y hY htight H (timeMap H hH) u₀

/-- A fixed random initial law also gives tight mild-path laws. The
initial state and convolution may be dependent; tightness of the two
marginals and joint continuity are sufficient. -/
theorem tight_random_initial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → RealL2) (hZ : Measurable Z)
    (Y : ℕ → Ω → C(Parameter, ℝ)) (hY : ∀ k, Measurable (Y k))
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (Y k))))
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ path H hH (Z sample) (Y k sample)))) :=
  MildPathTightness.tight_random_initial μ Z hZ Y hY htight H (timeMap H hH)

end SHEStochastic.NativeHeatPathTightness
