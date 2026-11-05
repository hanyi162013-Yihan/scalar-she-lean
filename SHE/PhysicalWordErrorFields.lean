module

public import SHE.PhysicalWordApproximationError
public import SHE.ActualMeanKernelJoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution SmoothApproximation ScalarData
local instance physicalWordErrorFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X W : Type} [MeasurableSpace X] [MeasurableSpace W] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

theorem capped_hessian_joint_measurable (k : ℕ) :
    Measurable (fun p:(ℝ×History X k)×WordRecursion.State (n+k)=>
      WordRecursion.hessian (ActualMeanKernel.cappedAverage L k p.1.1 p.1.2) p.2) := by
  change Measurable (fun p:(ℝ×History X k)×WordRecursion.State (n+k)=>
    GaussianTaylor.hessian (ActualMeanKernel.cappedAverage L k p.1.1 p.1.2) p.2)
  apply MeasurableDerivatives.hessian_measurable (n:=n+k)
    (F:=fun p:ℝ×History X k=>ActualMeanKernel.cappedAverage L k p.1 p.2)
    (ActualMeanKernel.cappedAverage_joint_measurable L k)
  intro p
  exact ((ActualMeanKernel.test_boundedSmooth L k p.2).average
    (ProbabilityTheory.multivariateGaussian (0:WordRecursion.State (n+k)) _)).smooth.of_le (by simp)

attribute [local irreducible] ActualMeanKernel.cappedAverage WordRecursion.hessian
  UncutSmoothWords.test WordRecursion.covariance

/-- The actual newest-factor discrepancy has a Borel inactive extension,
including dependent old means and spatial fields. -/
theorem approximationError_variable_measurable (D : ScalarData) (j k : ℕ)
    (p : W→History X k) (hp : Measurable p) (q : W→ℝ) (hq : Measurable q)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m)
    (a : W→HeatCircle→ℝ) (ha : Measurable (Function.uncurry a)) :
    Measurable (fun w:W×HeatCircle=>if q w.1<(carrier L k).terminal (p w.1) then
      approximationError L D j k (p w.1) (fun _=>a w.1 w.2) (q w.1) (m w.1) w.2 else 0) := by
  classical
  have hH:Measurable (fun w:W×HeatCircle=>WordRecursion.hessian
      (ActualMeanKernel.cappedAverage L k (q w.1) (p w.1)) (m w.1)):=
    (capped_hessian_joint_measurable L k).comp
    (((hq.comp measurable_fst).prodMk (hp.comp measurable_fst)).prodMk (hm.comp measurable_fst))
  have hr:Measurable (fun w:W×HeatCircle=>heatRow
      ((carrier L k).observations.observations (p w.1)) (q w.1) w.2):=
    (carrier L k).observations.heatRow_measurable.comp
      ((hp.comp measurable_fst).prodMk ((hq.comp measurable_fst).prodMk measurable_snd))
  have hbil:Measurable (fun w:W×HeatCircle=>WordRecursion.hessian
      (ActualMeanKernel.cappedAverage L k (q w.1) (p w.1)) (m w.1)
        (heatRow ((carrier L k).observations.observations (p w.1)) (q w.1) w.2)
        (heatRow ((carrier L k).observations.observations (p w.1)) (q w.1) w.2)):=
    ((continuous_fst.clm_apply continuous_snd).measurable.comp (hH.prodMk hr) |>.prodMk hr) |>
      (continuous_fst.clm_apply continuous_snd).measurable.comp
  have ho:Measurable (ApproximateCoefficientInsertion.originalTotal D):=by
    have he:ApproximateCoefficientInsertion.originalTotal D=
        fun z=>(ScalarReduction.additiveAmplitude D.lower)^2+D.residualCoefficient z:=
      funext (fun z=>(D.variance_split z).symm)
    rw [he]
    exact measurable_const.add D.residual_continuous.measurable
  have hs:Measurable (ApproximateCoefficientInsertion.smoothTotal D j):=
    measurable_const.add (D.smooth_boundedSmooth j).smooth.continuous.measurable
  have hv:=(((ho.comp ha).sub (hs.comp ha)).const_mul (1/2:ℝ)).mul hbil
  have hset:MeasurableSet {w:W×HeatCircle|q w.1<(carrier L k).terminal (p w.1)}:=
    measurableSet_lt (hq.comp measurable_fst) ((carrier L k).terminal_measurable.comp (hp.comp measurable_fst))
  convert! hv.ite hset measurable_const using 1
  funext w
  split_ifs with ht
  · simp only [approximationError,WordRecursion.directionalSecond,Pi.mul_apply,Pi.sub_apply,
      Function.comp_apply,Function.uncurry,ActualMeanKernel.cappedAverage,min_eq_left ht.le]
  · rfl
  all_goals exact Classical.decPred _

end SHE.PhysicalChainArrays
