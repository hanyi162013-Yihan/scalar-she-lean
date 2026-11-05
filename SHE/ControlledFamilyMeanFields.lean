module

public import SHE.ControlledThetaWeightedFields
public import SHE.FamilyMeanAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
noncomputable section

namespace SHE.ControlledFamilyMeanFields
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
  HistoryProductMeasure ActualMeanKernel NativeHeatObservation DyadicApproximation
open scoped NNReal ENNReal
local instance controlledFamilyMeanFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyMeanFields_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
local instance controlledFamilyMeanFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyMeanFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance controlledFamilyMeanFields_realSigma : MeasurableSpace RealL2 := borel _
local instance controlledFamilyMeanFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "Ref" => (fun a : ℝ×Inputs=>ControlledReferenceLevel.referenceData P A hA Λ a.1 v b hvb a.2)
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
variable {W : Type} [MeasurableSpace W]

/-- Joint scalar Borel structure of the literal mean kernel of the full
random-past interpolation family, in the orientation used by the Hilbert
operator. Both the law time and direction-row time may vary. -/
theorem familyWeightedField_measurable (a : W→ℝ×Inputs) (ha : Measurable a) (k : ℕ)
    (q r : W→ℝ) (hq : Measurable q) (hr : Measurable r)
    (m : W→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : W×History HeatCircle k=>m z.1 z.2))
    (t : W→Fin k→ℝ) (ht : Measurable t) :
    Measurable (familyWeightedField Ref Base a k (fun _=>Λ) q r m t) := by
  have hh := ControlledThetaWeightedFields.weightedSpatial_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : W×HeatCircle=>a z.1) (ha.comp measurable_fst)
    (fun z : W×HeatCircle=>q z.1) (fun z : W×HeatCircle=>r z.1)
    (hq.comp measurable_fst) (hr.comp measurable_fst)
    (fun z : W×HeatCircle=>m z.1)
    (hm.comp (measurable_fst.fst.prodMk measurable_snd))
    (fun z : W×HeatCircle=>t z.1) (ht.comp measurable_fst)
    (fun z : W×HeatCircle=>z.2) measurable_snd
  have he := hh.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)
  convert! he using 1

/-- The actual random-reference mean input is a genuine Borel map into
the native Hilbert space. All scalar-family measurability and coarse
section bounds are discharged by the actual recursion. -/
theorem meanInput_measurable (hΛ : 0≤Λ) (a : W→ℝ×Inputs) (ha : Measurable a) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (q : W→ℝ) (hq : Measurable q)
    (m : W→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : W×History HeatCircle k=>m z.1 z.2))
    (t : W→Fin k→ℝ) (ht : Measurable t) (V : W→RealL2) (hV : Measurable V) :
    Measurable (familyMeanInput Ref Base a k mass ρ hmass hρ (fun _=>Λ) q m t V) := by
  exact familyMeanInput_measurable Ref Base a k mass ρ hmass hρ (fun _=>Λ) q (fun _=>(b:ℝ))
    (fun _ _=>rfl) (fun _=>hΛ) m t
    (familyWeightedField_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm a ha k q q hq hq m hm t ht) V hV

end SHE.ControlledFamilyMeanFields
