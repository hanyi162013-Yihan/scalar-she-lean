module

public import SHEStochastic.MildPathTightness
public import SHEStochastic.GlobalHeatParameter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GlobalHeatPathTightness
open MeasureTheory SHE SHE.DyadicApproximation SHE.FiniteHaar HeatParameterCover HeatParameterPullback StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

def timeMap (H : ℝ≥0) (hH : 0<H) : C(Time H,ShortTime) :=
  ⟨GlobalHeatParameter.normalized H hH,GlobalHeatParameter.continuous_normalized H hH⟩

def path (H : ℝ≥0) (hH : 0<H) (u : RealL2) (Y : C(Parameter,ℝ)) : Path H RealL2 :=
  MildPathTightness.path H (timeMap H hH) u Y

theorem tight_random_initial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → RealL2) (hZ : Measurable Z) (Y : ℕ → Ω → C(Parameter,ℝ)) (hY : ∀ k, Measurable (Y k))
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (Y k)))) (H : ℝ≥0) (hH : 0<H) :
    IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ path H hH (Z sample) (Y k sample)))) :=
  MildPathTightness.tight_random_initial μ Z hZ Y hY htight H (timeMap H hH)

end SHEStochastic.GlobalHeatPathTightness
