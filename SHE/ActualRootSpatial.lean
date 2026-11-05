module
public import SHE.RootBackwardHessian
public import SHE.ActualVarianceLevel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ActualRootSpatial
open scoped NNReal
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  RootHeatBounds RootHeatTargets Filter Topology PhysicalIto PhysicalRemainderBound
local instance actualRootSpatial_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance actualRootSpatial_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance actualRootSpatial_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)(δ:ℝ)(hδ:0<δ)
variable (a:ℝ→ℝ)(ha:Measurable a){A:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

/-- The rough actual coefficient is evaluated at the FIXED current
field, so moving Gaussian words remain continuous in their heat age
without any continuity or derivative assumption on that coefficient. -/
theorem continuous_inserted (k:ℕ)(p:History P k)(ω:Ω){t:ℝ}
    (ht:t∈Ioo R.base ((level L δ hδ 0 k).terminal p))(x:HeatCircle):
    Continuous (fun ε:ℝ≥0=>insertedWord ((level L δ hδ ε k).window p)
      a (fun s=>U (ω,s)) (fun q=>X (ω,q)) ((level L δ hδ ε k).test p) t x):=by
  let Z:=fun ε:ℝ≥0=>(level L δ hδ ε k).observations.observations p
  let centers:=fun i=>(Z 0 i).center
  have htarg(ε:ℝ≥0)(i:Fin (n+k)):(level L δ hδ 0 k).terminal p≤(Z ε i).target:=by
    rw [←terminal_eq L δ hδ ε 0 k p]
    exact (level L δ hδ ε k).targets_after p i
  have hold:=ObservationTargetContinuity.continuous_observe Z centers
    (target_continuous L δ hδ k p) (fun ε i=>center_eq L δ hδ ε 0 k p i)
    t (fun ε i=>ht.2.trans_le (htarg ε i)) (fun s=>U (ω,s)) (fun q=>X (ω,q))
  have hH:=(RootBackwardHessian.continuous_backward_hessian L δ hδ k p t).comp
    (continuous_id.prodMk hold)
  have hr:Continuous (fun ε:ℝ≥0=>heatRow (Z ε) t x):=by
    apply (PiLp.continuous_toLp 2 (fun _:Fin (n+k)=>ℝ)).comp
    apply continuous_pi
    intro i
    exact CovarianceTargetContinuity.continuous_heatRow Z centers (target_continuous L δ hδ k p)
      (fun ε i=>center_eq L δ hδ ε 0 k p i) ht.2 htarg x i
  have hd:=(hH.clm_apply hr).clm_apply hr
  have hc:=(continuous_const (y:=(1/2:ℝ)*(a (X (ω,(t,x)))-R.reference (t,x)))).mul hd
  convert! hc using 1
  funext ε
  exact insertion_observe a R.reference (fun s=>U (ω,s)) (fun q=>X (ω,q)) (Z ε) t x _

def spatial (ε:ℝ≥0)(k:ℕ)(p:History P k)(ω:Ω)(t:ℝ):ℝ:=
  ∫x:HeatCircle,insertedWord ((level L δ hδ ε k).window p) a
    (fun s=>U (ω,s)) (fun q=>X (ω,q)) ((level L δ hδ ε k).test p) t x ∂haarAddCircle

include ha in
theorem spatial_measurable (hU:Measurable U)(hX:Measurable X)(ε:ℝ≥0)(k:ℕ):
    Measurable (fun q:(History P k×Ω)×ℝ=>spatial L δ hδ a U X ε k q.1.1 q.1.2 q.2):=
  (ActualVarianceLevel.insertion_measurable (level L δ hδ ε k) a ha U hU X hX).stronglyMeasurable.integral_prod_right'.measurable

include ha hAn hA in
theorem continuous_spatial (hU:Measurable U)(hX:Measurable X)
    (k:ℕ)(p:History P k)(ω:Ω){t:ℝ}
    (ht:t∈Ioo R.base ((level L δ hδ 0 k).terminal p)):
    Continuous (fun ε:ℝ≥0=>spatial L δ hδ a U X ε k p ω t):=by
  obtain ⟨C,_,hC⟩:=(test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩:=(test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩:=(test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let s:=(level L δ hδ 0 k).terminal p
  let Q:=Real.sqrt ((n+k:ℕ):ℝ)*CovarianceMatrix.heatRowBound (s-t)
  let K:=(1/2:ℝ)*(A+R.upper)*B*Q^2
  have hb(ε:ℝ≥0)(x:HeatCircle):
      ‖insertedWord ((level L δ hδ ε k).window p) a
        (fun s=>U (ω,s)) (fun q=>X (ω,q)) ((level L δ hδ ε k).test p) t x‖≤K:=by
    have hte:t∈Ioo ((level L δ hδ ε k).window p).left ((level L δ hδ ε k).window p).right:=by
      change t∈Ioo R.base ((level L δ hδ ε k).terminal p)
      rw [terminal_eq L δ hδ ε 0 k p]
      exact ht
    have hHb:∀z,‖GaussianTaylor.hessian (GaussianItoTest.backward
        ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) z‖≤B:=
      fun z=>BackwardRegularity.gaussian_state_hessian_bound _
        (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p)) z
    have hh:=inserted_pointwise_bound ((level L δ hδ ε k).window p) hAn hA hBn
      (fun s=>U (ω,s)) (fun q=>X (ω,q)) hte
      (GaussianItoTest.backward ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) hHb x
    have hr:‖heatRow ((level L δ hδ ε k).observations.observations p) t x‖≤Q:=
      UniformInsertions.heatRow_norm_bound ((level L δ hδ ε k).observations.observations p)
        (t:=t) (sub_pos.mpr ht.2) (fun i=>by
          have htar:=(level L δ hδ ε k).targets_after p i
          rw [terminal_eq L δ hδ ε 0 k p] at htar
          linarith) x
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2)
      (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAn R.upper_nonneg)) hBn))
  apply continuous_of_dominated (bound:=fun _:HeatCircle=>K)
  · intro ε
    exact ((ActualVarianceLevel.insertion_measurable (level L δ hδ ε k) a ha U hU X hX).comp
      ((measurable_const (a:=((p,ω),t))).prodMk measurable_id)).aestronglyMeasurable
  · exact fun ε=>Filter.Eventually.of_forall (hb ε)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (continuous_inserted L δ hδ a U X k p ω ht)

end SHE.ActualRootSpatial
