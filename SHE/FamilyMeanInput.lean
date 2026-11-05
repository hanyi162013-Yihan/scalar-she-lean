module

public import SHE.VariableMeanOperator
public import SHE.KernelActionFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel HistoryProductMeasure GaussianConvolution PhysicalMeanRange
open scoped ENNReal
local instance familyMeanInput_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance familyMeanInput_exponentFinite : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
local instance familyMeanInput_realSigma : MeasurableSpace RealL2 := borel _
local instance familyMeanInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance familyMeanInput_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance familyMeanInput_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {W A : Type} [MeasurableSpace W]
variable (R : A→ReferenceData) (L : (a : A)→CutoffWordLevel.Level (R a) HeatCircle 1)

def familyMeanInput (a : W→A) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : W→ℝ) (m : W→History HeatCircle k→WordRecursion.State (1+k))
    (t : W→Fin k→ℝ) (V : W→RealL2) (z : W) : CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (integralOperator (familyWeightedField R L a k damping q q m t) z (embed (V z)))

/-- True Hilbert-valued Borel realization of a variable-reference mean
field from its literal jointly Borel scalar kernel. Finite spatial caps
are derived on each parameter section and need not be uniform or measurable. -/
theorem familyMeanInput_measurable (a : W→A) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q T : W→ℝ) (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : W→History HeatCircle k→WordRecursion.State (1+k)) (t : W→Fin k→ℝ)
    (hF : Measurable (familyWeightedField R L a k damping q q m t))
    (V : W→RealL2) (hV : Measurable V) :
    Measurable (familyMeanInput R L a k mass ρ hmass hρ damping q m t V) := by
  have hb := family_weighted_bound_sections R L a k damping q q T hT hdamping m t
  have hh := action_measurable hF (fun z=>(hb z).imp (fun B hB=>hB.2))
    (fun z=>embed (V z)) (embed.continuous.measurable.comp hV)
  exact (OneInputOperator.besselHalf mass ρ hmass hρ).continuous.measurable.comp hh

theorem familyMeanInput_real (a : W→A) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q T : W→ℝ) (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : W→History HeatCircle k→WordRecursion.State (1+k)) (hm : ∀ z,Measurable (m z))
    (t : W→Fin k→ℝ) (V : W→RealL2) (z : W) :
    ∀ᵐ x ∂haarAddCircle,(familyMeanInput R L a k mass ρ hmass hρ damping q m t V z x).im=0 := by
  have hm' : Measurable (fun p : Unit×History HeatCircle k=>m z p.2) := (hm z).comp measurable_snd
  exact meanInput_real (L (a z)) (T z) (hT z) k mass ρ hmass hρ (hdamping z) (q z)
    (fun _ : Unit=>m z) hm' (fun _=>V z) (t z) ()

theorem familyMeanInput_realification (a : W→A) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q T : W→ℝ) (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : W→History HeatCircle k→WordRecursion.State (1+k)) (hm : ∀ z,Measurable (m z))
    (t : W→Fin k→ℝ) (V : W→RealL2) (z : W) :
    let F := familyMeanInput R L a k mass ρ hmass hρ damping q m t V z
    embed (NativeBesselReal.part F)=F ∧ ‖NativeBesselReal.part F‖=‖F‖ := by
  intro F
  have hreal := familyMeanInput_real R L a k mass ρ hmass hρ damping q T hT hdamping m hm t V z
  exact ⟨NativeBesselReal.embed_part F hreal,NativeBesselReal.part_norm F hreal⟩

end SHE.ActualMeanKernel
