module

public import SHE.NativeWordMeanDerivative
public import SHE.StoppedGaussianMarginals
public import SHE.HeatTreeAveraging

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! A literal n=1 physical heat-tree instantaneous mean-derivative estimate. The squared
old heat edge averages the actual old second-score root/rough Gaussian word derivative.
The newest covariance is the full native history with its own profile,
and its leaf marginal retains the leaf's own target age. -/
namespace SHE.NativeFirstWordMeanTree
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  HeatTorus HeatTorusKernel GaussianGramScore GaussianIncrement MeasurableGaussianScores
  NativeMeanFields NativeMeanAveraging NativeMeanScoreKernel MeasurableGeneralizedInverse
  GaussianWordFields NativeGaussianFirstWord GaussianAudit NativeOldRoot
  NativeWordMeanDerivative GaussianWordMeanDerivative HeatHistoryScore StoppedGaussianScore StoppedGaussianMarginals HeatTreeAveraging ProfileVariance
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2]

def relativeCenters (y:UnitAddCircle)(i:Fin 2):UnitAddCircle:=if i=0 then 0 else y

omit [MeasurableSpace HeatTorus.CircleL2] [BorelSpace HeatTorus.CircleL2] in
theorem relativeCenters_measurable (i:Fin 2):Measurable (fun y=>relativeCenters y i):=by
  classical
  by_cases hi:i=0 <;> simp only[relativeCenters,hi,ite_true,ite_false] <;> fun_prop

/-- The actual physical positive heat-tree average has one signed L² input.
All profiles and Gaussian means may depend on the relative heat coordinate.
No independent-kernel or spatial-supremum moment assumption is present. -/
theorem native_firstWord_heat_mean_derivative_energy:
    ∃h C:ℝ,0<h ∧ h≤1 ∧ 0<C ∧
      ∀(target:Fin 2→ℝ)(ht1:∀i,target i≤1)(Λ:ℝ),0<Λ→
      ∀(t:Fin 2→ℝ)(ht:∀i,0<t i),(∀i,t i≤h)→
      ∀(hage:∀i,target i=4*π^2*t i)(s:ℝ)(hs:0<s)(hmin:∀i,s≤target i)
      (c:(UnitAddCircle×UnitAddCircle)×Domain→ℝ)(hc:Measurable c)(U ell:ℝ)
      (hcb:∀p r,0≤c (p,r) ∧ c (p,r)≤U),0<ell→(∀p r,ell≤c (p,r))→
      ∀(d:HeatTorus.CircleL2)(m:UnitAddCircle×UnitAddCircle→State 2),Measurable m→
      ∀(δ:ℝ)(hδ:0<δ)(v:ℝ≥0)(f f' b:ℝ→ℝ)(A0 ν M H β:ℝ),
      0≤A0→0≤ν→(∀z,HasDerivAt f (f' z) z)→(∀z,|f z|≤A0)→(∀z,|f' z|≤A0*ν)→
      Measurable b→(∀z,|b z|≤M)→0≤H→0≤β→(∀z w,|b z-b w|≤H*|z-w|^β)→
      let act:∀i,0<target i:=fun i=>hs.trans_le (hmin i)
      let A:=covarianceField target relativeCenters c 0
      let D:=directionField target relativeCenters 0 Λ t (fun i=>by simpa using hage i) act (fun _=>d)
      let F:=fun p=>firstMeanScore (A p) (D p) v f b (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) (m p)
      let T:=4*A0*rootClipMass v ν*sqrt (H^2*(upperConstant*U*(target 1)^(1/2:ℝ))^β*gaussianAbsMoment (2*β))
      Integrable (fun x=>(∫y,‖HeatMarkov.kernel δ hδ y‖^2*F (y,x) ∂haarAddCircle)^2) haarAddCircle ∧
      (∫x,(∫y,‖HeatMarkov.kernel δ hδ y‖^2*F (y,x) ∂haarAddCircle)^2 ∂haarAddCircle)≤
        ‖unitHeatKernel δ 0‖^4*T^2*((C/ell)*(sqrt s)⁻¹)*‖d‖^2:=by
  obtain ⟨h,C,hh,hh1,hC,he⟩:=native_firstWord_mean_derivative_energy 2 (by norm_num)
  refine ⟨h,C,hh,hh1,hC,?_⟩
  intro target ht1 Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d m hm
    δ hδ v f f' b A0 ν M H β hA0 hν hf hfb hfD hb hbB hH hβ hholder
  let act:∀i,0<target i:=fun i=>hs.trans_le (hmin i)
  let A:=covarianceField target relativeCenters c 0
  let D:=directionField target relativeCenters 0 Λ t (fun i=>by simpa using hage i) act (fun _=>d)
  let F:=fun p=>firstMeanScore (A p) (D p) v f b (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) (m p)
  let T:=4*A0*rootClipMass v ν*sqrt (H^2*(upperConstant*U*(target 1)^(1/2:ℝ))^β*gaussianAbsMoment (2*β))
  have hd:Measurable (fun _:UnitAddCircle=>d):=measurable_const
  have hid:Integrable (fun _:UnitAddCircle=>‖d‖^2) (heatSquareMeasure δ hδ):=integrable_const _
  have hW (p:UnitAddCircle×UnitAddCircle):
      Var[EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2);multivariateGaussian 0 (A p)]≤
        upperConstant*U*(target 1)^(1/2:ℝ):=
    native_coordinate_variance_bound target (nativeCenter (fun i=>relativeCenters p.1 i+p.2))
      act ht1 (fun r=>c (p,r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb p) 1
  have hword:=he (heatSquareMeasure δ hδ) target relativeCenters relativeCenters_measurable 0 Λ hΛ
    t ht hth (fun i=>by simpa using hage i) s hs (fun i=>by simpa using hmin i)
    c hc U ell hcb hell hcl (fun _=>d) hd hid m hm v f f' b
    (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) A0 ν M H β
    (upperConstant*U*(target 1)^(1/2:ℝ)) hA0 hν hf hfb hfD hb hbB hH hβ hholder hW
  have hAm:Measurable A:=covarianceField_measurable target relativeCenters relativeCenters_measurable c hc 0
  have hDm:Measurable D:=directionField_measurable target relativeCenters relativeCenters_measurable 0 Λ t ht
    (fun i=>by simpa using hage i) act (fun _=>d) measurable_const
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hFm:Measurable F:=
    firstMeanScore_field_measurable A hAm D m hDm hm v f b hfc hb _ _
  have havg:=heat_square_average δ hδ F hFm hword.1
  refine ⟨havg.1,havg.2.trans ?_⟩
  have hhword:=mul_le_mul_of_nonneg_left hword.2 (sq_nonneg ‖unitHeatKernel δ 0‖)
  simp only[integral_const,smul_eq_mul,heatSquareMeasure_mass] at hhword
  convert! hhword using 1
  ring

end SHE.NativeFirstWordMeanTree
