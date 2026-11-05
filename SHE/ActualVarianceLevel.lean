module
public import SHE.CutoffWordAnalytic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ActualVarianceLevel
open Set MeasureTheory StoppedFourier WordRecursion CovarianceEndpoint GaussianItoTest
  CutoffWordLevel IntegratedPhysicalStep PhysicalIto UniformSmooth
local instance actualVarianceLevel_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
variable [MeasurableSpace CircleL2][BorelSpace CircleL2]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)
variable (a:ℝ→ℝ)(ha:Measurable a)
variable (U:Ω×ℝ→CircleL2)(hU:Measurable U)
variable (X:Ω×(ℝ×HeatCircle)→ℝ)(hX:Measurable X)
variable (N:P→(ℝ→WordRecursion.State n→ℝ)→Ω→ℝ)

/-- The physical bracket coefficient is independent of the smooth
coefficient used to generate the deterministic reference words. -/
def data:LevelData P Ω n where
  window:=L.window
  totalVariance:=a
  state:=fun _ ω t=>U (ω,t)
  field:=fun _ ω p=>X (ω,p)
  test:=L.test
  stochasticTerm:=N

include ha hU hX in
set_option backward.isDefEq.respectTransparency true in
theorem insertion_measurable:
    Measurable (fun p:((P×Ω)×ℝ)×HeatCircle=>insertedWord (L.window p.1.1.1)
      a (fun t=>U (p.1.1.2,t)) (fun q=>X (p.1.1.2,q)) (L.test p.1.1.1) p.1.2 p.2):=by
  have hY:Measurable (fun p:((P×Ω)×ℝ)×HeatCircle=>
      observe (fun t=>U (p.1.1.2,t)) (fun q=>X (p.1.1.2,q))
        (L.observations.observations p.1.1.1) p.1.2):=
    (CutoffWordAnalytic.physical_observe_measurable L hU hX).comp measurable_fst
  have hG:Measurable (fun p:(P×ℝ)×WordRecursion.State n=>
      GaussianTaylor.hessian (backward (L.window p.1.1) (L.test p.1.1) p.1.2) p.2):=
    MeasurableDerivatives.hessian_measurable (CutoffWordAnalytic.backward_measurable L)
      (fun p=>((CutoffWordAnalytic.backward_uniform L).smooth p).of_le (by simp))
  have hH:=hG.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk hY)
  have hrmap:Measurable (fun p:((P×Ω)×ℝ)×HeatCircle=>(p.1.1.1,(p.1.2,p.2))):=
    measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hr:=L.observations.heatRow_measurable.comp hrmap
  have he₁:Continuous (fun p:(WordRecursion.State n→L[ℝ]WordRecursion.State n→L[ℝ]ℝ)×WordRecursion.State n=>p.1 p.2):=
    continuous_fst.clm_apply continuous_snd
  have he₂:Continuous (fun p:(WordRecursion.State n→L[ℝ]ℝ)×WordRecursion.State n=>p.1 p.2):=
    continuous_fst.clm_apply continuous_snd
  have hd:=he₂.measurable.comp ((he₁.measurable.comp (hH.prodMk hr)).prodMk hr)
  have hc:Measurable (fun p:((P×Ω)×ℝ)×HeatCircle=>
      a (X (p.1.1.2,(p.1.2,p.2)))-R.reference (p.1.2,p.2)):=
    (ha.comp (hX.comp (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd)))).sub
      (R.reference_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  convert! (hc.const_mul (1/2:ℝ)).mul hd using 1
  funext p
  exact insertion_observe a R.reference (fun t=>U (p.1.1.2,t)) (fun q=>X (p.1.1.2,q))
    (L.observations.observations p.1.1.1) p.1.2 p.2 _

include ha hU hX in
theorem remainder_measurable:
    Measurable (fun p:P×Ω=>(data L a U X N).remainder p.1 p.2):=by
  have hi:=(insertion_measurable L a ha U hU X hX).stronglyMeasurable.integral_prod_right'
    (ν:=AddCircle.haarAddCircle)
  have hs:MeasurableSet {p:(P×Ω)×ℝ|R.base<p.2∧p.2≤L.terminal p.1.1}:=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (L.terminal_measurable.comp measurable_fst.fst))
  have hm:Measurable (fun p:(P×Ω)×ℝ=>if R.base<p.2∧p.2≤L.terminal p.1.1 then
      ∫y,insertedWord (L.window p.1.1) a (fun t=>U (p.1.2,t))
        (fun q=>X (p.1.2,q)) (L.test p.1.1) p.2 y ∂AddCircle.haarAddCircle else 0):=
    hi.measurable.ite hs measurable_const
  have ht:=hm.stronglyMeasurable.integral_prod_right' (ν:=volume)
  convert! ht.measurable using 1
  funext p
  change (∫t in R.base..L.terminal p.1,_) = _
  rw [intervalIntegral.integral_of_le (L.terminal_base p.1),←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Set.indicator,mem_Ioc]
  rfl

include ha hU hX in
theorem analyticConditions {A:ℝ}(hA:0≤A)(hb:∀z,|a z|≤A):
    AnalyticConditions (data L a U X N):=by
  refine ⟨ha,⟨A,R.upper,R.horizon,hA,R.upper_nonneg,R.base_nonneg.trans R.ordered,
    hb,(fun _=>le_rfl),(fun _=>R.base_nonneg),L.terminal_horizon⟩,L.test_uniform,?_,?_,?_⟩
  · exact CutoffWordAnalytic.physical_leaf_measurable L hU hX N
  · exact CutoffWordAnalytic.physical_reference_measurable L hU hX N
  · exact remainder_measurable L a ha U hU X hX N

end SHE.ActualVarianceLevel
