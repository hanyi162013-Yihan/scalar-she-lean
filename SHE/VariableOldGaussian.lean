module

public import SHE.GaussianWordMeanDerivative
public import SHE.OldFractionHeatScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Joint Borel old Gaussian fractions and newest word scores when the old
interval and its variance vary. This supplies actual time measurability,
rather than an assumed measurable score choice. -/
namespace SHE.VariableOldGaussian
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores NativeOldRoot
  GaussianCovarianceWord GaussianRoughMoments ProfileL2 GaussianScoreKernel
  NativeGaussianFirstWord GaussianWordFields GaussianWordMeanDerivative ProfileVariance
  OldFractionHeatScale
open scoped InnerProductSpace NNReal
variable {X:Type*}[MeasurableSpace X]{n:ℕ}

def scalarKernel (v:X→ℝ≥0)(hv:Measurable v):Kernel X ℝ where
  toFun x:=gaussianReal 0 (v x)
  measurable':=measurable_gaussianReal.comp (measurable_const.prodMk hv)

instance scalarKernel_markov (v:X→ℝ≥0)(hv:Measurable v):IsMarkovKernel (scalarKernel v hv) where
  isProbabilityMeasure _:=by change IsProbabilityMeasure (gaussianReal 0 _);infer_instance

theorem oldRoot_field_measurable (v:X→ℝ≥0)(hv:Measurable v)(f:ℝ→ℝ)(hf:Measurable f)
    (m:X→ℝ)(hm:Measurable m):Measurable (fun x=>oldRoot (v x) f (m x)):=by
  have hs:Measurable (fun p:X×ℝ=>GaussianAudit.secondScore (v p.1) p.2*f (m p.1+p.2)):=by
    unfold GaussianAudit.secondScore
    exact (((measurable_snd.pow_const 2).sub ((measurable_coe_nnreal_real.comp hv).comp measurable_fst)).div
      (((measurable_coe_nnreal_real.comp hv).comp measurable_fst).pow_const 2)).mul
      (hf.comp ((hm.comp measurable_fst).add measurable_snd))
  exact (hs.stronglyMeasurable.integral_kernel_prod_right' (κ:=scalarKernel v hv)).measurable

def positiveOldVariance (ell:ℝ)(r:ℝ):ℝ≥0:=(positiveVarianceMap (fun _=>ell) (r,0)).toNNReal

theorem positiveOldVariance_measurable (ell:ℝ):Measurable (positiveOldVariance ell):=
  (measurable_real_toNNReal.comp
    ((positiveVarianceMap_measurable (c:=fun _=>ell) measurable_const).comp
      (measurable_id.prodMk measurable_const)))

theorem positiveOldVariance_eq (ell:ℝ){r:ℝ}(hr:0≤r):positiveOldVariance ell r=oldVariance ell r:=by
  unfold positiveOldVariance oldVariance
  rw[positiveVarianceMap_eq hr]

/-- Joint Borel instantaneous newest mean mark, with the old variance
varying on the same parameter as the full newest covariance and input. -/
theorem firstMeanScore_variable_variance_measurable
    (A:X→Mat n)(hA:Measurable A)(D m:X→State n)(hD:Measurable D)(hm:Measurable m)
    (v:X→ℝ≥0)(hv:Measurable v)(f a:ℝ→ℝ)(hf:Measurable f)(ha:Measurable a)
    (K L:State n→L[ℝ] ℝ):
    Measurable (fun x=>firstMeanScore (A x) (D x) (v x) f a K L (m x)):=by
  have hshift:Measurable (fun p:X×State n=>m p.1+p.2):=(hm.comp measurable_fst).add measurable_snd
  have hb:Measurable (fun p:X×State n=>oldRoot (v p.1) f (K (m p.1+p.2))):=
    oldRoot_field_measurable _ (hv.comp measurable_fst) f hf _ (K.continuous.measurable.comp hshift)
  have har:Measurable (fun p:X×State n=>a (L (m p.1+p.2))):=
    ha.comp (L.continuous.measurable.comp hshift)
  have hmb:Measurable (fun x=>GaussianCovarianceWord.average (A x) (fun y=>oldRoot (v x) f (K y)) (m x)):=
    (hb.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable
  have hma:Measurable (fun x=>GaussianCovarianceWord.average (A x) (fun y=>a (L y)) (m x)):=
    (har.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable
  have hcenter:Measurable (fun p:X×State n=>centeredTest (A p.1)
      (fun y=>oldRoot (v p.1) f (K y)) (fun y=>a (L y)) (m p.1) p.2):=
    (hb.sub (hmb.comp measurable_fst)).mul (har.sub (hma.comp measurable_fst))
  have hscore:Measurable (fun p:X×State n=>firstScore (A p.1) (D p.1) p.2):=by
    convert! (firstScore_measurable (n:=n)).comp
      (((hA.prodMk hD).comp (measurable_fst:Measurable (Prod.fst:X×State n→X))).prodMk measurable_snd) using 1
  exact ((hcenter.mul hscore).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=gaussianKernel A hA)).measurable

end SHE.VariableOldGaussian
