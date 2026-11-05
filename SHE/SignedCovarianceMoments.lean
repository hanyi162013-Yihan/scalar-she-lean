module

public import SHE.SignedInputMoments
public import SHE.FiniteWordScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.SignedCovarianceMoments
open Set Filter MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianConvolution
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]

/-- Joint Borel dependence of the actual second-score average, including
singular covariance and arbitrary dependent current means. -/
theorem score_average_measurable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (row : X→State n) (hrow : Measurable row) (F : State n→ℝ) (hF : Measurable F)
    (m : Ω→State n) (hm : Measurable m) :
    Measurable (fun z : Ω×X=>∫ y,F (m z.1+y)*
      MeasurableGaussianScores.secondScore A (row z.2) y ∂multivariateGaussian 0 A) := by
  have hscore : Measurable (fun z : (Ω×X)×State n=>
      MeasurableGaussianScores.secondScore A (row z.1.2) z.2) := by
    convert! MeasurableGaussianScores.secondScore_measurable.comp
      (((measurable_const.prodMk hrow).comp measurable_fst.snd).prodMk measurable_snd) using 1
  have harg : Measurable (fun z : (Ω×X)×State n=>m z.1.1+z.2) :=
    (hm.comp measurable_fst.fst).add measurable_snd
  have hf : Measurable (fun z : (Ω×X)×State n=>F (m z.1.1+z.2)*
      MeasurableGaussianScores.secondScore A (row z.1.2) z.2) := by
    convert! (hF.comp harg).mul hscore using 1
  exact (hf.stronglyMeasurable.integral_prod_right').measurable

/-- The literal covariance derivative has an actual signed continuum input.
All averaging integrability follows from the weighted score mass and the
pointwise even moments, including on zero-score sets. -/
theorem covariance_even_moment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (row : X→State n) (F : State n→ℝ) (m : Ω→State n)
    (hjoint : Measurable (fun z : Ω×X=>∫ y,F (m z.1+y)*
      MeasurableGaussianScores.secondScore A (row z.2) y ∂multivariateGaussian 0 A))
    (e : X→ℝ) (he : Measurable e)
    (hV : Measurable (fun x=>MeasurableGaussianScores.scoreVariance A (row x)))
    (hVpos : ∀ᵐ x ∂ν,0≤MeasurableGaussianScores.scoreVariance A (row x))
    (hEnergy : Integrable (fun x=>|e x| *MeasurableGaussianScores.scoreVariance A (row x)) ν)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C) (b : ℕ) (hb : 0<b)
    (hi : ∀ᵐ x ∂ν,Integrable (fun ω=>|∫ y,F (m ω+y)*
      MeasurableGaussianScores.secondScore A (row x) y ∂multivariateGaussian 0 A|^(2*b)) μ)
    (hbound : ∀ᵐ x ∂ν,(∫ ω,|∫ y,F (m ω+y)*
      MeasurableGaussianScores.secondScore A (row x) y ∂multivariateGaussian 0 A|^(2*b) ∂μ)≤
      C*(MeasurableGaussianScores.scoreVariance A (row x)*K)^(2*b)) :
    Integrable (fun ω=>|FiniteWordScores.covarianceMark ν A e row F (m ω)|^(2*b)) μ ∧
      (∫ ω,|FiniteWordScores.covarianceMark ν A e row F (m ω)|^(2*b) ∂μ)≤
        C*(((1/2:ℝ)*K)*∫ x,|e x| *MeasurableGaussianScores.scoreVariance A (row x) ∂ν)^(2*b) := by
  let G : Ω×X→ℝ := fun z=>∫ y,F (m z.1+y)*MeasurableGaussianScores.secondScore A (row z.2) y
    ∂multivariateGaussian 0 A
  have hh := SignedInputMoments.weighted_even_moment μ ν G hjoint _ e hV he hVpos hEnergy hK hC b hb hi hbound
  have hpow (ω : Ω) : |FiniteWordScores.covarianceMark ν A e row F (m ω)|^(2*b)=
      (1/2:ℝ)^(2*b)*|∫ x,e x*G (ω,x) ∂ν|^(2*b) := by
    simp only [FiniteWordScores.covarianceMark,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow]
    rfl
  constructor
  · exact (hh.1.const_mul _).congr (ae_of_all _ (fun ω=>(hpow ω).symm))
  · simp_rw [hpow]
    rw [integral_const_mul]
    have hz := mul_le_mul_of_nonneg_left hh.2 (show 0≤(1/2:ℝ)^(2*b) by positivity)
    exact hz.trans_eq (by simp only [mul_pow]; ring)

end SHE.SignedCovarianceMoments
