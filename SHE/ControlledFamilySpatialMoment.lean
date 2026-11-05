module

public import SHE.ParentMeanMass
public import SHE.ControlledFamilyMeanFields
public import SHE.ConditionalSpatialMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFamilySpatialMoment
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
  HistoryProductMeasure ActualMeanKernel PhysicalParentGeometry PhysicalScoreChain ScalarMeanEnvelope
open scoped NNReal
local instance controlledFamilySpatialMoment_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilySpatialMoment_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilySpatialMoment_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State 1=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
variable {Ω : Type} [MeasurableSpace Ω]

/-- Conditional old-space averaging of the literal moving-reference
kernel. The deterministic parent heat density is integrated BEFORE its
moment power, preserving all gap powers and the exact past-event mass.
The old reference and every current mean may depend on that same past. -/
theorem on_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (a : Ω→ℝ×Inputs) (ha : Measurable a) (k : ℕ)
    (m : Ω→History X k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History X k=>m z.1 z.2))
    (q r : ℝ) (t : Fin k→ℝ) (x : X) (y : HeatCircle)
    (hp : StrictHistory (Base (0,(0,0))) k (separated k (x,t,fun _=>0)))
    (hr : r<(carrier (Base (0,(0,0))) k).terminal (separated k (x,t,fun _=>0)))
    (D C : ℝ) (hD : 0≤D) (hC : 0≤C) (order : ℕ) (horder : 0<order)
    (event : Set Ω) (hevent : MeasurableSet event)
    (hpoint : ∀ᵐ z : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle (T:=2*Real.pi)),
      Integrable (fun ω=>|weightedPoint (Base (a ω)) k Λ q r (m ω) (separated k (x,t,z)) y|^(2*order)) (μ.restrict event) ∧
      (∫ ω in event,|weightedPoint (Base (a ω)) k Λ q r (m ω) (separated k (x,t,z)) y|^(2*order) ∂μ)≤
        C*(D*ParentMeanDensity.globalDensity (Base (0,(0,0))) k (separated k (x,t,z)) r y)^(2*order)*μ.real event) :
    Integrable (fun ω=>‖weightedSpatial (Base (a ω)) k Λ q r (fun _ : Unit=>m ω) t () y x‖^(2*order)) (μ.restrict event) ∧
      (∫ ω in event,‖weightedSpatial (Base (a ω)) k Λ q r (fun _ : Unit=>m ω) t () y x‖^(2*order) ∂μ)≤
        C*(D*massBudget (Base (0,(0,0))) k (separated k (x,t,fun _=>0)) 1 r y)^(2*order)*μ.real event := by
  let L0:=Base (0,(0,0))
  let p0:=separated k (x,t,fun _=>(0:HeatCircle))
  let ν:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let G : Ω×(Fin k→HeatCircle)→ℝ:=fun z=>weightedPoint (Base (a z.1)) k Λ q r
    (m z.1) (separated k (x,t,z.2)) y
  have hh : Measurable (fun z : Ω×(Fin k→HeatCircle)=>separated k (x,t,z.2)) :=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_snd))
  have hG : Measurable G := ControlledThetaWeightedFields.weightedPoint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : Ω×(Fin k→HeatCircle)=>a z.1) (ha.comp measurable_fst) _ hh
    (fun _=>q) (fun _=>r) measurable_const measurable_const
    (fun z=>m z.1 (separated k (x,t,z.2))) (hm.comp (measurable_fst.prodMk hh))
    (fun _=>y) measurable_const
  let Hgeom := fun z : Fin k→HeatCircle=>D*ParentMeanDensity.density L0 k p0 r y z
  have hden := ParentMeanDensity.density_mass_bound L0 hages k p0 hp hr y
  have hHm : Measurable Hgeom := measurable_const.mul
    (ParentMeanDensity.density_continuous L0 hages k p0 hp hr y).measurable
  have hHi : Integrable Hgeom ν := hden.1.const_mul D
  have hH0 (z : Fin k→HeatCircle) : 0≤Hgeom z :=
    mul_nonneg hD (ParentMeanDensity.globalDensity_nonneg L0 k _ r y)
  have hpoint' : ∀ᵐ z ∂ν,Integrable (fun ω=>|G (ω,z)|^(2*order)) (μ.restrict event) ∧
      (∫ ω in event,|G (ω,z)|^(2*order) ∂μ)≤C*(Hgeom z)^(2*order)*μ.real event := by
    filter_upwards [hpoint] with z hz
    simpa only [G,Hgeom,ParentMeanDensity.density,replaceSpace_separated,L0,p0] using hz
  have hj := ConditionalSpatialMoments.on_event μ ν G hG Hgeom hHm hHi hH0 order horder C hC event hevent
    (hpoint'.mono (fun _ hz=>hz.1)) (hpoint'.mono (fun _ hz=>hz.2))
  have hmass : (∫ z,Hgeom z ∂ν)≤D*massBudget L0 k p0 1 r y := by
    rw [show Hgeom=(fun z=>D*ParentMeanDensity.density L0 k p0 r y z) from rfl,integral_const_mul]
    exact mul_le_mul_of_nonneg_left hden.2 hD
  refine ⟨by simpa only [weightedSpatial,G,Complex.norm_real,Real.norm_eq_abs] using hj.1,?_⟩
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (integral_nonneg hH0) hmass (2*order)) hC)
      (measureReal_nonneg (μ:=μ) (s:=event))
  simpa only [weightedSpatial,G,Complex.norm_real,Real.norm_eq_abs] using hj.2.trans hb

end SHE.ControlledFamilySpatialMoment
