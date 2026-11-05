module

public import SHE.RootJointHeatLeafLimit
public import SHE.HeatFieldTestLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.ScalarRootHeatLeaf
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open JointWordAnalytic RootHeatBounds NativeHeatObservation Filter Topology
open DyadicApproximation
open scoped NNReal ENNReal
local instance scalarRootHeatLeaf_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance scalarRootHeatLeaf_realSigma : MeasurableSpace RealL2 := borel _
local instance scalarRootHeatLeaf_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance scalarRootHeatLeaf_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance scalarRootHeatLeaf_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

def scalarState (r : ℝ) : WordRecursion.State 1 := WithLp.toLp 2 (fun _ => r)

theorem scalarState_sub_norm (r s : ℝ) : ‖scalarState r-scalarState s‖=|r-s| := by
  rw [EuclideanSpace.norm_eq]
  simp [scalarState,Real.norm_eq_abs,Real.sqrt_sq_eq_abs]

theorem scalarState_continuous : Continuous scalarState := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp
  exact continuous_pi (fun _ => continuous_id)

variable {R : ReferenceData} (L : Level R HeatCircle 1)
variable (T : ℝ) (hterm : ∀ x,L.terminal x=T)
variable (hstop : ∀ x,(L.observations.observations x 0).stop=T)
variable (htarget : ∀ x,(L.observations.observations x 0).target=T)
variable (hcenter : ∀ x,(L.observations.observations x 0).center=x)

def scalarTest (p : HeatCircle×ℝ) : ℝ := L.test p.1 (scalarState p.2)

theorem scalarTest_measurable : Measurable (scalarTest L) :=
  L.test_measurable.comp (measurable_fst.prodMk (scalarState_continuous.measurable.comp measurable_snd))

theorem scalarTest_bounds : ∃ M D : ℝ,0≤M ∧ 0≤D ∧
    (∀ x z,|scalarTest L (x,z)|≤M) ∧
    (∀ x z w,|scalarTest L (x,z)-scalarTest L (x,w)|≤D*|z-w|) := by
  obtain ⟨M,hM,hMb⟩ := L.test_uniform.norm_bound
  obtain ⟨D,hD,hDb⟩ := L.test_uniform.fderiv.norm_bound
  refine ⟨M,D,hM,hD,fun x z => by simpa only [scalarTest,Real.norm_eq_abs] using hMb x (scalarState z),?_⟩
  intro x z w
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (L.test_uniform.smooth x).differentiable (by simp) y)
    (fun y _ => hDb x y) convex_univ (mem_univ (scalarState w)) (mem_univ (scalarState z))
  simpa only [scalarTest,Real.norm_eq_abs,scalarState_sub_norm] using hh

variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ]
variable {h : ℝ≥0} (dU dV : PredictableWordState.Data 𝓕 τ h) (Λ : ℝ)

include hterm hstop htarget hcenter in
theorem shifted_leaf_eq {ε : ℝ} (hε : 0<ε) (x : HeatCircle) (ω : Ω) :
    JointWordAnalytic.leaf (shift L ε.toNNReal) Λ dU.physicalState dV.physicalState
      dU.physicalField dV.physicalField x ω=
      scalarTest L (x,PhysicalProfile.physicalHeatMean (dV.physicalState (ω,T)) (ε,x)) := by
  have he : ((ε.toNNReal:ℝ≥0):ℝ)=ε := Real.coe_toNNReal _ hε.le
  unfold JointWordAnalytic.leaf
  change L.test x (state (shift L ε.toNNReal) Λ _ _ _ _ x ω (L.terminal x))=_
  rw [hterm x]
  congr 1
  apply PiLp.ext
  intro i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  unfold state JointWordObserve.evaluate
  simp only [WithLp.ofLp_toLp]
  change observe _ _ _ T 0+Real.exp (-Λ*((L.observations.observations x 0).stop-T))*
    (observe _ _ _ T 0-observe _ _ _ T 0)=_
  rw [hstop x,sub_self,mul_zero,Real.exp_zero,one_mul]
  have hobs (m : PredictableWordState.Data 𝓕 τ h) :
      observe (fun t => m.physicalState (ω,t)) (fun tx => m.physicalField (ω,tx))
        ((shift L ε.toNNReal).observations.observations x) T 0=
      PhysicalProfile.physicalHeatMean (m.physicalState (ω,T)) (ε,x) := by
    change (if T<(L.observations.observations x 0).target+(ε.toNNReal:ℝ) then _ else _)=_
    rw [htarget x,he,if_pos (by linarith)]
    dsimp only [RootHeatBounds.shift]
    rw [htarget x,hcenter x,he]
    congr 2
    ring
  rw [hobs dV,hobs dU]
  simp only [scalarTest,scalarState,WithLp.ofLp_toLp]
  ring

include hterm hstop htarget hcenter in
theorem literal_leaf_eq (x : HeatCircle) (ω : Ω) :
    JointWordAnalytic.leaf L Λ dU.physicalState dV.physicalState
      dU.physicalField dV.physicalField x ω=
      scalarTest L (x,dV.physicalField (ω,(T,x))) := by
  unfold JointWordAnalytic.leaf
  rw [hterm x]
  congr 1
  apply PiLp.ext
  intro i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  change (observe _ _ _ T 0)+Real.exp (-Λ*((L.observations.observations x 0).stop-T))*
    (observe _ _ _ T 0-observe _ _ _ T 0)=_
  rw [hstop x,sub_self,mul_zero,Real.exp_zero,one_mul]
  have hobs (m : PredictableWordState.Data 𝓕 τ h) :
      observe (fun t => m.physicalState (ω,t)) (fun tx => m.physicalField (ω,tx))
        (L.observations.observations x) T 0=m.physicalField (ω,(T,x)) := by
    change (if T<(L.observations.observations x 0).target then _ else _)=_
    rw [htarget x,if_neg (lt_irrefl T),hcenter x]
  rw [hobs dU,hobs dV]
  simp only [scalarState,WithLp.ofLp_toLp]
  ring

include hterm hstop htarget hcenter in
/-- The actual scalar native root is reached in sample/spatial L¹.
The canonical scalar field is used only spatially almost everywhere;
no point evaluation continuity on L² is presumed. -/
theorem integrated_root_difference_tendsto_zero :
    Tendsto (fun ε : ℝ => ∫ q : HeatCircle×Ω,
      |JointWordAnalytic.leaf (shift L ε.toNNReal) Λ dU.physicalState dV.physicalState
          dU.physicalField dV.physicalField q.1 q.2-
        JointWordAnalytic.leaf L Λ dU.physicalState dV.physicalState
          dU.physicalField dV.physicalField q.1 q.2| ∂haarAddCircle.prod τ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let V : Ω→RealL2 := fun ω => dV.state (T.toNNReal,ω)
  have hV : Measurable V :=
    (dV.state_predictable.mono (PredictableL2.predictable_le_product 𝓕)).measurable.comp
      (measurable_const.prodMk measurable_id)
  obtain ⟨M,D,hM,hD,hMb,hDb⟩ := scalarTest_bounds L
  have ht := HeatFieldTestLimit.integrated_error_tendsto_zero V hV (scalarTest L)
    (scalarTest_measurable L) τ hMb hD hDb
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let f : HeatCircle×Ω→ℝ := fun q =>
    |JointWordAnalytic.leaf (shift L ε.toNNReal) Λ dU.physicalState dV.physicalState
        dU.physicalField dV.physicalField q.1 q.2-
      JointWordAnalytic.leaf L Λ dU.physicalState dV.physicalState
        dU.physicalField dV.physicalField q.1 q.2|
  have hf : Measurable f :=
    ((JointWordAnalytic.leaf_measurable _ Λ dU.physicalState_measurable dV.physicalState_measurable
      dU.physicalField_measurable dV.physicalField_measurable).sub
      (JointWordAnalytic.leaf_measurable _ Λ dU.physicalState_measurable dV.physicalState_measurable
      dU.physicalField_measurable dV.physicalField_measurable)).norm
  have hi : Integrable f (haarAddCircle.prod τ) := by
    apply (integrable_const (2*M)).mono' hf.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs,abs_abs]
    rw [shifted_leaf_eq L T hterm hstop htarget hcenter dU dV Λ hε,
      literal_leaf_eq L T hterm hstop htarget hcenter dU dV Λ]
    exact (abs_sub _ _).trans ((add_le_add (hMb _ _) (hMb _ _)).trans_eq (by ring))
  change (∫ ω,HeatFieldTestLimit.error V (scalarTest L) ε ω ∂τ)=∫ q,f q ∂haarAddCircle.prod τ
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards with ω
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  rw [shifted_leaf_eq L T hterm hstop htarget hcenter dU dV Λ hε,
    literal_leaf_eq L T hterm hstop htarget hcenter dU dV Λ]
  rfl

end SHE.ScalarRootHeatLeaf
