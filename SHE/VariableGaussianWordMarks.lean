module

public import SHE.GaussianWordCovarianceBound
public import SHE.VariableOldGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Literal Borel word and continuum covariance-mark fields with varying
old scalar variance, newest covariance, means, and physical profile input.
All these fields may depend on the same history parameters. -/
namespace SHE.VariableGaussianWordMarks
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores NativeOldRoot
  GaussianCovarianceWord GaussianWordAffine GaussianScoreKernel NativeGaussianFirstWord
  GaussianWordFields VariableOldGaussian
open scoped InnerProductSpace NNReal
variable {P X:Type*}[MeasurableSpace P][MeasurableSpace X]{n:ℕ}

theorem firstWord_variable_variance_measurable
    (A:P→Mat n)(hA:Measurable A)(m:P→State n)(hm:Measurable m)
    (v:P→ℝ≥0)(hv:Measurable v)(f a:ℝ→ℝ)(hf:Measurable f)(ha:Measurable a)
    (K L:State n→L[ℝ] ℝ):
    Measurable (fun p=>firstWord (A p) (v p) f a K L (m p)):=by
  have hs:Measurable (fun p:P×State n=>m p.1+p.2):=(hm.comp measurable_fst).add measurable_snd
  have hb:Measurable (fun p:P×State n=>oldRoot (v p.1) f (K (m p.1+p.2))):=
    oldRoot_field_measurable _ (hv.comp measurable_fst) f hf _ (K.continuous.measurable.comp hs)
  have har:Measurable (fun p:P×State n=>a (L (m p.1+p.2))):=
    ha.comp (L.continuous.measurable.comp hs)
  exact ((hb.mul har).stronglyMeasurable.integral_kernel_prod_right'
      (κ:=gaussianKernel A hA)).measurable.sub
    ((hb.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable.mul
      (har.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable)

def secondWordScore (A:Mat n)(D:State n)(v:ℝ≥0)(f a:ℝ→ℝ)
    (K L:State n→L[ℝ] ℝ)(m:State n):ℝ:=
  ∫y,centeredTest A (fun z=>oldRoot v f (K z)) (fun z=>a (L z)) m y*
    secondScore A D y ∂multivariateGaussian 0 A

theorem secondWordScore_variable_variance_measurable
    (A:P→Mat n)(hA:Measurable A)(D m:P→State n)(hD:Measurable D)(hm:Measurable m)
    (v:P→ℝ≥0)(hv:Measurable v)(f a:ℝ→ℝ)(hf:Measurable f)(ha:Measurable a)
    (K L:State n→L[ℝ] ℝ):
    Measurable (fun p=>secondWordScore (A p) (D p) (v p) f a K L (m p)):=by
  have hshift:Measurable (fun p:P×State n=>m p.1+p.2):=(hm.comp measurable_fst).add measurable_snd
  have hb:Measurable (fun p:P×State n=>oldRoot (v p.1) f (K (m p.1+p.2))):=
    oldRoot_field_measurable _ (hv.comp measurable_fst) f hf _ (K.continuous.measurable.comp hshift)
  have har:Measurable (fun p:P×State n=>a (L (m p.1+p.2))):=
    ha.comp (L.continuous.measurable.comp hshift)
  have hmb:Measurable (fun p=>GaussianCovarianceWord.average (A p) (fun y=>oldRoot (v p) f (K y)) (m p)):=
    (hb.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable
  have hma:Measurable (fun p=>GaussianCovarianceWord.average (A p) (fun y=>a (L y)) (m p)):=
    (har.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable
  have hcenter:Measurable (fun p:P×State n=>centeredTest (A p.1)
      (fun y=>oldRoot (v p.1) f (K y)) (fun y=>a (L y)) (m p.1) p.2):=
    (hb.sub (hmb.comp measurable_fst)).mul (har.sub (hma.comp measurable_fst))
  have hscore:Measurable (fun p:P×State n=>secondScore (A p.1) (D p.1) p.2):=by
    convert! (secondScore_measurable (n:=n)).comp
      (((hA.prodMk hD).comp (measurable_fst:Measurable (Prod.fst:P×State n→P))).prodMk measurable_snd) using 1
  exact ((hcenter.mul hscore).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=gaussianKernel A hA)).measurable

/-- Joint measurability of the actual signed continuum covariance word,
with no independence between the profile, history, means, or old variance. -/
theorem covarianceMark_variable_variance_measurable (μ:Measure X)[SFinite μ]
    (A:P→Mat n)(hA:Measurable A)(m:P→State n)(hm:Measurable m)
    (v:P→ℝ≥0)(hv:Measurable v)(e:P×X→ℝ)(he:Measurable e)
    (D:P×X→State n)(hD:Measurable D)(f a:ℝ→ℝ)(hf:Measurable f)(ha:Measurable a)
    (K L:State n→L[ℝ] ℝ):
    Measurable (fun p=>covarianceMark μ (A p) (fun x=>e (p,x)) (fun x=>D (p,x))
      (fun y=>oldRoot (v p) f (K y)) (fun y=>a (L y)) (m p)):=by
  have hs:=secondWordScore_variable_variance_measurable
    (fun p:P×X=>A p.1) (hA.comp measurable_fst) D (fun p=>m p.1) hD (hm.comp measurable_fst)
    (fun p=>v p.1) (hv.comp measurable_fst) f a hf ha K L
  exact (((he.mul hs).stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable.const_mul (1/2:ℝ))

end SHE.VariableGaussianWordMarks
