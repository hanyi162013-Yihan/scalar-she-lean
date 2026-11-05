module

public import SHE.ControlledFamilySpatialMoment
public import SHE.ControlledFamilyKernelBounds
public import SHE.HistoryInputSections
public import SHE.StrictHistoryFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFamilyHistoryMoments
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
  HistoryProductMeasure ActualMeanKernel PhysicalParentGeometry PhysicalScoreChain ScalarMeanEnvelope
open scoped NNReal
local instance controlledFamilyHistoryMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyHistoryMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyHistoryMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State 1=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
variable {Ω : Type} [MeasurableSpace Ω]

/-- Joint history/input disintegration and density Jensen for the
literal moving-reference word. The row time may depend on the same
history before Fubini; no separately AE fixed-row theorem is evaluated
at an adaptive time or center. -/
theorem spatial_history_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (root : Measure X) [IsFiniteMeasure root]
    (a : Ω→ℝ×Inputs) (ha : Measurable a) (k : ℕ)
    (m : Ω→History X k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History X k=>m z.1 z.2))
    (q : ℝ) (r D : History X k→ℝ) (hr : Measurable r) (hD : Measurable D)
    (hD0 : ∀ p,0≤D p) (hri : ∀ p x,r (replaceSpace k p x)=r p)
    (hDi : ∀ p x,D (replaceSpace k p x)=D p)
    (Good : History X k→Prop) (hGood : MeasurableSet {p | Good p})
    (hGi : ∀ p x,Good (replaceSpace k p x)↔Good p)
    (C : ℝ) (hC : 0≤C) (order : ℕ) (horder : 0<order)
    (hpoint : ∀ᵐ p ∂historyMeasure
        (ControlledReferenceLevel.referenceData P A hA Λ 0 v b hvb (0,0)) root k,
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        Good p ∧ StrictHistory (Base (0,(0,0))) k p ∧ r p<(carrier (Base (0,(0,0))) k).terminal p →
        (∫ ω,|weightedPoint (Base (a ω)) k Λ q (r p) (m ω) p y|^(2*order) ∂μ)≤
          C*(D p*ParentMeanDensity.globalDensity (Base (0,(0,0))) k p (r p) y)^(2*order)) :
    ∀ᵐ x ∂root,∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      let p0:=separated k (x,t,fun _=>(0:HeatCircle))
      Good p0 → ∀ hp : StrictHistory (Base (0,(0,0))) k p0,
        r p0<(carrier (Base (0,(0,0))) k).terminal p0 →
        ∀ᵐ y : HeatCircle ∂haarAddCircle,
          Integrable (fun ω=>‖weightedSpatial (Base (a ω)) k Λ q (r p0) (fun _ : Unit=>m ω) t () y x‖^(2*order)) μ ∧
            (∫ ω,‖weightedSpatial (Base (a ω)) k Λ q (r p0) (fun _ : Unit=>m ω) t () y x‖^(2*order) ∂μ)≤
              C*(D p0*massBudget (Base (0,(0,0))) k p0 1 (r p0) y)^(2*order) := by
  let L0:=Base (0,(0,0))
  let R0:=ControlledReferenceLevel.referenceData P A hA Λ 0 v b hvb (0,0)
  let K : Ω×(History X k×HeatCircle)→ℝ:=fun z=>weightedPoint (Base (a z.1)) k Λ q (r z.2.1)
    (m z.1) z.2.1 z.2.2
  have hK : Measurable K := ControlledThetaWeightedFields.weightedPoint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : Ω×(History X k×HeatCircle)=>a z.1) (ha.comp measurable_fst)
    (fun z=>z.2.1) measurable_snd.fst (fun _=>q) (fun z=>r z.2.1) measurable_const (hr.comp measurable_snd.fst)
    (fun z=>m z.1 z.2.1) (hm.comp (measurable_fst.prodMk measurable_snd.fst))
    (fun z=>z.2.2) measurable_snd.snd
  have hmoment:=measurable_abs_moment μ K hK (2*order)
  have hbound : Measurable (fun z : History X k×HeatCircle=>
      C*(D z.1*ParentMeanDensity.globalDensity L0 k z.1 (r z.1) z.2)^(2*order)) :=
    (((hD.comp measurable_fst).mul (ParentMeanDensity.globalDensity_variable_measurable L0 k r hr)).pow_const _).const_mul C
  let E : History X k×HeatCircle→Prop:=fun z=>
    Good z.1 ∧ StrictHistory L0 k z.1 ∧ r z.1<(carrier L0 k).terminal z.1 →
      (∫ ω,|K (ω,z)|^(2*order) ∂μ)≤C*(D z.1*ParentMeanDensity.globalDensity L0 k z.1 (r z.1) z.2)^(2*order)
  have hactive : MeasurableSet {z : History X k×HeatCircle |
      Good z.1 ∧ StrictHistory L0 k z.1 ∧ r z.1<(carrier L0 k).terminal z.1} :=
    (hGood.preimage measurable_fst).inter (((strictHistory_measurableSet L0 k).preimage measurable_fst).inter
      (measurableSet_lt (hr.comp measurable_fst) ((carrier L0 k).terminal_measurable.comp measurable_fst)))
  have hE : MeasurableSet {z | E z} := by
    convert hactive.compl.union (measurableSet_le hmoment hbound) using 1
    ext z
    simp only [E,mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or]
  have hs:=ae_input_sections R0 root k E hE hpoint
  filter_upwards [hs] with x hx
  filter_upwards [hx] with t ht
  intro p0 hg hp hrow
  filter_upwards [ht] with y hy
  have hh := ControlledFamilySpatialMoment.on_event P A hA Λ v b hvb Z htarget hstop F hF hFm μ
    hages a ha k m hm q (r p0) t x y hp hrow (D p0) C (hD0 p0) hC order horder univ MeasurableSet.univ
  obtain ⟨B,hB,hcoarse⟩:=ControlledFamilyKernelBounds.weightedPoint_family_uniform_bound
    P A hA Λ v b hvb Z htarget hstop F hF hFm k hΛ q (r p0) t
  have hpt : ∀ᵐ z : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle (T:=2*Real.pi)),
      Integrable (fun ω=>|weightedPoint (Base (a ω)) k Λ q (r p0) (m ω) (separated k (x,t,z)) y|^(2*order)) (μ.restrict univ) ∧
      (∫ ω in univ,|weightedPoint (Base (a ω)) k Λ q (r p0) (m ω) (separated k (x,t,z)) y|^(2*order) ∂μ)≤
        C*(D p0*ParentMeanDensity.globalDensity L0 k (separated k (x,t,z)) (r p0) y)^(2*order)*μ.real univ := by
    filter_upwards [hy] with z hz
    have hpx : separated k (x,t,z)=replaceSpace k p0 z := (replaceSpace_separated k x t (fun _=>0) z).symm
    have hstrict : StrictHistory L0 k (separated k (x,t,z)) := by rw [hpx];exact (replaceSpace_strict_iff L0 k p0 z).mpr hp
    have hgood : Good (separated k (x,t,z)) := by rw [hpx];exact (hGi p0 z).mpr hg
    have hrow' : r (separated k (x,t,z))<(carrier L0 k).terminal (separated k (x,t,z)) := by
      simpa only [hpx,hri,replaceSpace_terminal] using hrow
    have hineq:=hz ⟨hgood,hstrict,hrow'⟩
    have hi : Integrable (fun ω=>|weightedPoint (Base (a ω)) k Λ q (r p0) (m ω) (separated k (x,t,z)) y|^(2*order)) μ := by
      have hzm:=hK.comp (measurable_id.prodMk (measurable_const (a:=(separated k (x,t,z),y))))
      have hzm' : Measurable (fun ω=>weightedPoint (Base (a ω)) k Λ q (r p0) (m ω) (separated k (x,t,z)) y) := by
        simpa only [K,Function.comp_def,id_eq,hpx,hri] using hzm
      apply (integrable_const (B^(2*order))).mono' (hzm'.norm.pow_const _).aestronglyMeasurable
      exact ae_of_all _ (fun ω=>by
        rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hcoarse (a ω) (m ω) y x z) _)
    refine ⟨by simpa only [Measure.restrict_univ] using hi,?_⟩
    simpa only [E,K,hpx,hri,hDi,Measure.restrict_univ,probReal_univ,mul_one] using hineq
  simpa only [Measure.restrict_univ,probReal_univ,mul_one] using hh hpt

end SHE.ControlledFamilyHistoryMoments
