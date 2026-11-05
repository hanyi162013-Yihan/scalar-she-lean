module

public import SHE.SignedCovarianceMoments
public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHE.VariableFiniteMarkFields
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement GaussianConvolution
  StoppedFourier StoppedGaussianFeatures
open scoped NNReal
local instance variableFiniteMarkFields_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X] {n : ℕ}

/-- The complete bounded or unbounded finite test may vary with every
history and noise parameter; the actual Gaussian covariance may change rank. -/
theorem second_average_measurable
    (A : W→Matrix (Fin n) (Fin n) ℝ) (hA : Measurable A)
    (F : W×State n→ℝ) (hF : Measurable F) (m : W→State n) (hm : Measurable m)
    (row : W×X→State n) (hrow : Measurable row) :
    Measurable (fun p : W×X=>∫ y,F (p.1,m p.1+y)*
      MeasurableGaussianScores.secondScore (A p.1) (row p) y ∂multivariateGaussian 0 (A p.1)) := by
  have hs : Measurable (fun z : (W×X)×State n=>m z.1.1+z.2) :=
    (hm.comp measurable_fst.fst).add measurable_snd
  have htest : Measurable (fun z : (W×X)×State n=>F (z.1.1,m z.1.1+z.2)) := by
    convert! hF.comp (measurable_fst.fst.prodMk hs) using 1
  have hscore : Measurable (fun z : (W×X)×State n=>
      MeasurableGaussianScores.secondScore (A z.1.1) (row z.1) z.2) := by
    convert! MeasurableGaussianScores.secondScore_measurable.comp
      ((((hA.comp measurable_fst).prodMk hrow).comp measurable_fst).prodMk measurable_snd) using 1
  exact ((htest.mul hscore).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=GaussianScoreKernel.gaussianKernel (fun p : W×X=>A p.1) (hA.comp measurable_fst))).measurable

/-- Joint Borel dependence of the literal complete covariance mark for any
sigma-finite physical input measure and dependent coefficient/profile fields. -/
theorem covariance_mark_measurable (ν : Measure X) [SFinite ν]
    (A : W→Matrix (Fin n) (Fin n) ℝ) (hA : Measurable A)
    (F : W×State n→ℝ) (hF : Measurable F) (m : W→State n) (hm : Measurable m)
    (row : W×X→State n) (hrow : Measurable row) (e : W×X→ℝ) (he : Measurable e) :
    Measurable (fun p=>FiniteWordScores.covarianceMark ν (A p) (fun x=>e (p,x))
      (fun x=>row (p,x)) (fun y=>F (p,y)) (m p)) := by
  have hG := second_average_measurable A hA F hF m hm row hrow
  convert! ((he.mul hG).stronglyMeasurable.integral_prod_right' (ν:=ν)).measurable.const_mul (1/2:ℝ) using 1

/-- The moving lower history cutoff is kept literally inside its own
physical history measure. No pointwise family is evaluated on an AE diagonal. -/
theorem history_covariance_mark_measurable
    (A : W→Matrix (Fin n) (Fin n) ℝ) (hA : Measurable A)
    (F : W×State n→ℝ) (hF : Measurable F) (m : W→State n) (hm : Measurable m)
    (row : W×Domain→State n) (hrow : Measurable row) (e : W×Domain→ℝ) (he : Measurable e)
    (q : W→ℝ) (hq : Measurable q) :
    Measurable (fun p=>FiniteWordScores.covarianceMark (historyMeasure (q p)) (A p) (fun x=>e (p,x))
      (fun x=>row (p,x)) (fun y=>F (p,y)) (m p)) := by
  have hG := second_average_measurable A hA F hF m hm row hrow
  have hset : MeasurableSet {p : W×Domain | q p.1≤p.2.1} :=
    measurableSet_le (hq.comp measurable_fst) measurable_snd.fst
  have hh : Measurable (fun p : W×Domain=>if q p.1≤p.2.1 then
      e p*(∫ y,F (p.1,m p.1+y)*MeasurableGaussianScores.secondScore (A p.1) (row p) y
        ∂multivariateGaussian 0 (A p.1)) else 0) := (he.mul hG).ite hset measurable_const
  have hi := (hh.stronglyMeasurable.integral_prod_right'
    (ν:=volume.prod (haarAddCircle (T:=2*π)))).measurable.const_mul (1/2:ℝ)
  convert! hi using 1
  funext p
  unfold FiniteWordScores.covarianceMark historyMeasure
  rw [Measure.restrict_prod_eq_prod_univ,←integral_indicator
    (measurableSet_Ici.prod MeasurableSet.univ)]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  simp only [Set.indicator,mem_prod,mem_Ici,mem_univ,and_true]

end SHE.VariableFiniteMarkFields
