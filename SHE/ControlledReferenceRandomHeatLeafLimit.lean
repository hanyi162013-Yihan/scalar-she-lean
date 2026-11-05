module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.ControlledReferenceRecursiveAverages
public import SHE.ControlledReferenceRecursiveWeights
public import SHE.HeatFieldMovingWeight
public import SHE.ControlledReferenceRandomSpatialLimit
public import SHE.ControlledReferenceHeatChildren
public import SHE.JointHeatLeafLimit
public import SHE.ProductIntegralCycle
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointStateSpatialLimit
public import SHE.PastParameterDiagonal
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRandomHeatLeafLimit
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open Filter Topology
open scoped NNReal
local instance controlledReferenceRandomHeatLeafLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRandomHeatLeafLimit_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRandomHeatLeafLimit_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local instance controlledReferenceRandomHeatLeafLimit_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ] {H : ℝ≥0}
variable (dU dV : PredictableWordState.Data 𝓕 τ H)

local notation "U" => dU.physicalState
local notation "V" => dV.physicalState
local notation "XU" => dU.physicalField
local notation "XV" => dV.physicalField
local notation "R₀" => R (0,0)
variable (u : Ω→Inputs) (hu : StronglyMeasurable u)

def leaf (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) : ℝ :=
  JointWordAnalytic.leaf (L (u ω) ε k) Λ U V XU XV h ω

include hsmall hu in
theorem leaf_measurable (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : History Unit k×Ω => leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV u ε k q.1 q.2) := by
  let Q := History Unit k×Ω
  let K := fun (p : Inputs) (q : Q) => JointWordAnalytic.leaf (L p ε k) Λ U V XU XV q.1 q.2
  have hK (p : Inputs) : Measurable (K p) := JointWordAnalytic.leaf_measurable (L p ε k) Λ
    dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hh := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl K hK huQ
    (fun q => ControlledReferenceRecursiveFields.continuous_leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ ε k q.1 q.2)
  exact hh.measurable

include hsmall hu in
/-- The spatial newest-leaf correction is placed in the genuine full
history/sample measure, retaining its random-reference Hessian weight. -/
theorem integrated_spatial_difference_tendsto_zero (hΛ : 0≤Λ)
    (ν : Measure Unit) [IsFiniteMeasure ν] (k : ℕ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Tendsto (fun ε : ℝ => ∫ q : History Unit (k+1)×Ω,
      |JointCutoffStep.heatChildLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV ε q.1 q.2-
        JointCutoffStep.childLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV q.1 q.2|
      ∂(CutoffWordHistories.historyMeasure R₀ ν (k+1)).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := ControlledReferenceRandomSpatialLimit.integrated_child_difference_tendsto_zero P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall dU dV hΛ u hu ν k μ
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceHeatChildren.children_bound P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV k
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
  let f := fun (h : History Unit k) (z : ℝ×HeatCircle) (ω : Ω) =>
    |JointCutoffStep.heatChildLeaf (L (u ω) ε.toNNReal k) Λ δ U V XU XV ε (h,z) ω-
      JointCutoffStep.childLeaf (L (u ω) ε.toNNReal k) Λ δ U V XU XV (h,z) ω|
  have hheat := ControlledReferenceHeatChildren.heatChild_diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV
    dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hΛ u hu ε.toNNReal k
  rw [he] at hheat
  have hlit := ControlledReferenceLiteralChildren.childLeaf_diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV
    dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hΛ u hu ε.toNNReal k
  have hm : Measurable (fun q : (History Unit k×(ℝ×HeatCircle))×Ω => f q.1.1 q.1.2 q.2) := (hheat.sub hlit).norm
  have hp : Measurable (fun q : ((History Unit k×Ω)×ℝ)×HeatCircle => ((q.1.1.1,(q.1.2,q.2)),q.1.1.2)) :=
    (measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)).prodMk measurable_fst.fst.snd
  have hi : Integrable (fun q : ((History Unit k×Ω)×ℝ)×HeatCircle => f q.1.1.1 (q.1.2,q.2) q.1.1.2)
      ((((CutoffWordHistories.historyMeasure R₀ ν k).prod μ).prod (volume.restrict (Ioc (v:ℝ) (b:ℝ)))).prod AddCircle.haarAddCircle) := by
    apply (integrable_const (2*C)).mono' (hm.comp hp).aestronglyMeasurable
    filter_upwards with q
    dsimp only [f,Function.comp_def,Prod.fst,Prod.snd]
    rw [Real.norm_eq_abs,abs_abs]
    have hh := (hC (u q.1.1.2) ε.toNNReal (q.1.1.1,(q.1.2,q.2)) q.1.1.2).1
    rw [he] at hh
    exact (norm_sub_le _ _).trans ((add_le_add hh (hC (u q.1.1.2) ε.toNNReal (q.1.1.1,(q.1.2,q.2)) q.1.1.2).2).trans_eq (by ring))
  exact (ProductIntegralCycle.integral_cycle_iterated (CutoffWordHistories.historyMeasure R₀ ν k)
    (volume.restrict (Ioc (v:ℝ) (b:ℝ))) AddCircle.haarAddCircle μ f hi).symm

include hsmall hu in
/-- Actual recursively heat-regularized leaves with a genuine random
reference converge in full finite-history/sample L¹ at every fixed
smooth depth and fixed time cutoff. No pointwise zero-age assertion or
uniformity as the time cutoff/depth varies is used. -/
theorem integrated_leaf_difference_tendsto_zero (hΛ : 0≤Λ)
    (ν : Measure Unit) [IsFiniteMeasure ν] (depth : ℕ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Tendsto (fun ε : ℝ => ∫ q : History Unit depth×Ω,
      |leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV u ε.toNNReal depth q.1 q.2-
        leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV u 0 depth q.1 q.2|
      ∂(CutoffWordHistories.historyMeasure R₀ ν depth).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  cases depth with
  | zero =>
    have he : (fun ε : ℝ => ∫ q : History Unit 0×Ω,
        |leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV u ε.toNNReal 0 q.1 q.2-
          leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV u 0 0 q.1 q.2|
        ∂(CutoffWordHistories.historyMeasure R₀ ν 0).prod μ)=fun _ => 0 := by
      funext ε
      simp only [leaf,ControlledReferenceRecursiveBounds.level,RecursiveHeatBounds.level,HeatCutoffHistories.iterate,sub_self,abs_zero,integral_zero]
    rw [he]
    exact tendsto_const_nhds
  | succ k =>
    have hs := integrated_spatial_difference_tendsto_zero P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall dU dV u hu hΛ ν k μ
    have hl := ControlledReferenceLiteralChildren.literalChild_converges P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV
      dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hΛ u hu k
      (CutoffWordHistories.historyMeasure R₀ ν (k+1)) μ
    have ht := hs.add hl
    simp only [add_zero] at ht
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) ?_ ht
    obtain ⟨C,hCn,hC⟩ := ControlledReferenceHeatChildren.children_bound P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV k
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have he : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
    let σ := (CutoffWordHistories.historyMeasure R₀ ν (k+1)).prod μ
    let f := fun q : History Unit (k+1)×Ω =>
      |JointCutoffStep.heatChildLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV ε q.1 q.2-
        JointCutoffStep.childLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV q.1 q.2|
    let g := fun q : History Unit (k+1)×Ω =>
      |JointCutoffStep.childLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV q.1 q.2-
        JointCutoffStep.childLeaf (L (u q.2) 0 k) Λ δ U V XU XV q.1 q.2|
    have hheat := ControlledReferenceHeatChildren.heatChild_diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV
      dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hΛ u hu ε.toNNReal k
    rw [he] at hheat
    have hlit (η : ℝ≥0) := ControlledReferenceLiteralChildren.childLeaf_diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV
      dU.physicalState_measurable dV.physicalState_measurable dU.physicalField_measurable dV.physicalField_measurable hΛ u hu η k
    have hfm : Measurable f := (hheat.sub (hlit ε.toNNReal)).norm
    have hgm : Measurable g := ((hlit ε.toNNReal).sub (hlit 0)).norm
    have hfi : Integrable f σ := by
      apply (integrable_const (2*C)).mono' hfm.aestronglyMeasurable
      filter_upwards with q
      rw [Real.norm_eq_abs,abs_abs]
      have hh := (hC (u q.2) ε.toNNReal q.1 q.2).1
      rw [he] at hh
      exact (norm_sub_le _ _).trans ((add_le_add hh (hC (u q.2) ε.toNNReal q.1 q.2).2).trans_eq (by ring))
    have hgi : Integrable g σ := by
      apply (integrable_const (2*C)).mono' hgm.aestronglyMeasurable
      filter_upwards with q
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hC (u q.2) ε.toNNReal q.1 q.2).2 (hC (u q.2) 0 q.1 q.2).2).trans_eq (by ring))
    rw [← integral_add hfi hgi]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (hfi.add hgi)
    filter_upwards with q
    change |JointCutoffStep.heatChildLeaf (L (u q.2) ε.toNNReal k) Λ δ U V XU XV ε.toNNReal q.1 q.2-
      JointCutoffStep.heatChildLeaf (L (u q.2) 0 k) Λ δ U V XU XV 0 q.1 q.2|≤_
    rw [he,JointHeatLeafLimit.heatChild_zero_eq_literal (δ := δ) (Λ := Λ)]
    exact abs_sub_le _ _ _

end SHE.ControlledReferenceRandomHeatLeafLimit
