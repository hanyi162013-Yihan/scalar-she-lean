module

public import SHE.FamilyMeanInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel HistoryProductMeasure
open scoped ENNReal
local instance familyMeanAverage_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance familyMeanAverage_exponentFinite : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
local instance familyMeanAverage_realSigma : MeasurableSpace RealL2 := borel _
local instance familyMeanAverage_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance familyMeanAverage_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance familyMeanAverage_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P W A : Type} [MeasurableSpace P] [MeasurableSpace W]
variable (R : A→ReferenceData) (L : (a : A)→CutoffWordLevel.Level (R a) HeatCircle 1)

def familyMeanAverage (ν : Measure P) (a : P×W→A) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : P×W→ℝ) (m : P×W→History HeatCircle k→WordRecursion.State (1+k))
    (t : P×W→Fin k→ℝ) (V : P×W→RealL2) (z : W) : CircleL2 :=
  ∫ p,familyMeanInput R L a k mass ρ hmass hρ damping q m t V (p,z) ∂ν

/-- Old-time or interpolation integration is a genuine Bochner vector
average of the literal variable-reference mean field. In particular its
joint current-time/sample Borel structure is retained. -/
theorem familyMeanAverage_measurable (ν : Measure P) [SFinite ν] (a : P×W→A) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q T : P×W→ℝ) (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : P×W→History HeatCircle k→WordRecursion.State (1+k)) (t : P×W→Fin k→ℝ)
    (hF : Measurable (familyWeightedField R L a k damping q q m t))
    (V : P×W→RealL2) (hV : Measurable V) :
    Measurable (familyMeanAverage R L ν a k mass ρ hmass hρ damping q m t V) :=
  (familyMeanInput_measurable R L a k mass ρ hmass hρ damping q T hT hdamping m t hF V hV).stronglyMeasurable.integral_prod_left'.measurable

theorem familyMeanAverage_real (ν : Measure P) (a : P×W→A) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q T : P×W→ℝ) (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : P×W→History HeatCircle k→WordRecursion.State (1+k))
    (hm : ∀ z,Measurable (m z)) (t : P×W→Fin k→ℝ) (V : P×W→RealL2) (z : W) :
    ∀ᵐ x ∂haarAddCircle,(familyMeanAverage R L ν a k mass ρ hmass hρ damping q m t V z x).im=0 :=
  NativeBesselReal.integral_real ν _
    (fun p=>familyMeanInput_real R L a k mass ρ hmass hρ damping q T hT hdamping m hm t V (p,z))

theorem familyMeanAverage_realification (ν : Measure P) (a : P×W→A) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q T : P×W→ℝ) (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : P×W→History HeatCircle k→WordRecursion.State (1+k))
    (hm : ∀ z,Measurable (m z)) (t : P×W→Fin k→ℝ) (V : P×W→RealL2) (z : W) :
    let F := familyMeanAverage R L ν a k mass ρ hmass hρ damping q m t V z
    embed (NativeBesselReal.part F)=F ∧ ‖NativeBesselReal.part F‖=‖F‖ := by
  intro F
  have hreal := familyMeanAverage_real R L ν a k mass ρ hmass hρ damping q T hT hdamping m hm t V z
  exact ⟨NativeBesselReal.embed_part F hreal,NativeBesselReal.part_norm F hreal⟩

end SHE.ActualMeanKernel
