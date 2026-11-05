module

public import SHE.MeasurableGaussianScores
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Genuine Gaussian kernels with rank-varying covariance and canonical
score moments under their composition-product law. This keeps arbitrary
parameter dependence rather than replacing it by independence. -/
namespace SHE.GaussianScoreKernel
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit
  MeasurableGeneralizedInverse MeasurableGaussianScores
open scoped InnerProductSpace

variable {X:Type*} [MeasurableSpace X] {n:ℕ}

def gaussianKernel (A:X→Mat n) (hA:Measurable A) : Kernel X (State n) where
  toFun x:=multivariateGaussian 0 (A x)
  measurable':=measurable_multivariateGaussian.comp (measurable_const.prodMk hA)

instance gaussianKernel_markov (A:X→Mat n) (hA:Measurable A) :
    IsMarkovKernel (gaussianKernel A hA) where
  isProbabilityMeasure x:=by change IsProbabilityMeasure (multivariateGaussian 0 (A x));infer_instance

private theorem nonnegative_compProd (ν:Measure X) [SFinite ν] (κ:Kernel X (State n)) [IsSFiniteKernel κ]
    (f:X×State n→ℝ) (hf:Measurable f) (hpos:∀p,0≤f p)
    (J:X→ℝ) (hJ:Integrable J ν)
    (hfib:∀x,Integrable (fun y=>f (x,y)) (κ x)) (hvalue:∀x,(∫y,f (x,y) ∂κ x)=J x) :
    Integrable f (ν⊗ₘκ) ∧ (∫p,f p ∂ν⊗ₘκ)=∫x,J x ∂ν := by
  have hn:Integrable (fun x=>∫y,‖f (x,y)‖ ∂κ x) ν:=by
    convert! hJ using 1
    funext x
    rw[←hvalue x]
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>Real.norm_of_nonneg (hpos (x,y)))
  have hi:Integrable f (ν⊗ₘκ):=(Measure.integrable_compProd_iff hf.aestronglyMeasurable).mpr
    ⟨ae_of_all _ hfib,hn⟩
  refine ⟨hi,?_⟩
  rw[Measure.integral_compProd hi]
  exact integral_congr_ae (ae_of_all _ hvalue)

theorem firstScore_kernel_even_moments (ν:Measure X) [SFinite ν]
    (A:X→Mat n) (hA:Measurable A) (hpos:∀x,(A x).PosSemidef)
    (d:X→State n) (hd:Measurable d)
    (hrange:∀x,d x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A x)).range) (p:ℕ)
    (hV:Integrable (fun x=>scoreVariance (A x) (d x)^p) ν) :
    Integrable (fun z:X×State n=>|firstScore (A z.1) (d z.1) z.2|^(2*p)) (ν⊗ₘgaussianKernel A hA) ∧
      (∫z:X×State n,|firstScore (A z.1) (d z.1) z.2|^(2*p) ∂ν⊗ₘgaussianKernel A hA)=
        (∫x,scoreVariance (A x) (d x)^p ∂ν)*firstScoreMoment p := by
  have hm:Measurable (fun z:X×State n=>firstScore (A z.1) (d z.1) z.2):=by
    convert! (firstScore_measurable (n:=n)).comp
      (((hA.prodMk hd).comp (measurable_fst : Measurable (Prod.fst : X×State n→X))).prodMk measurable_snd) using 1
  have hi:=nonnegative_compProd ν (gaussianKernel A hA)
    (fun z=>|firstScore (A z.1) (d z.1) z.2|^(2*p)) ((continuous_abs.measurable.comp hm).pow_const _) (fun _=>by positivity)
    (fun x=>scoreVariance (A x) (d x)^p*firstScoreMoment p) (hV.mul_const _)
    (fun x=>(firstScore_even_moments (hpos x) (hrange x) p).1)
    (fun x=>(firstScore_even_moments (hpos x) (hrange x) p).2)
  exact ⟨hi.1,hi.2.trans (integral_mul_const _ _)⟩

theorem secondScore_kernel_even_moments (ν:Measure X) [SFinite ν]
    (A:X→Mat n) (hA:Measurable A) (hpos:∀x,(A x).PosSemidef)
    (d:X→State n) (hd:Measurable d)
    (hrange:∀x,d x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A x)).range) (p:ℕ)
    (hV:Integrable (fun x=>scoreVariance (A x) (d x)^(2*p)) ν) :
    Integrable (fun z:X×State n=>|secondScore (A z.1) (d z.1) z.2|^(2*p)) (ν⊗ₘgaussianKernel A hA) ∧
      (∫z:X×State n,|secondScore (A z.1) (d z.1) z.2|^(2*p) ∂ν⊗ₘgaussianKernel A hA)=
        (∫x,scoreVariance (A x) (d x)^(2*p) ∂ν)*secondScoreMoment p := by
  have hm:Measurable (fun z:X×State n=>secondScore (A z.1) (d z.1) z.2):=by
    convert! (secondScore_measurable (n:=n)).comp
      (((hA.prodMk hd).comp (measurable_fst : Measurable (Prod.fst : X×State n→X))).prodMk measurable_snd) using 1
  have hi:=nonnegative_compProd ν (gaussianKernel A hA)
    (fun z=>|secondScore (A z.1) (d z.1) z.2|^(2*p)) ((continuous_abs.measurable.comp hm).pow_const _) (fun _=>by positivity)
    (fun x=>scoreVariance (A x) (d x)^(2*p)*secondScoreMoment p) (hV.mul_const _)
    (fun x=>(secondScore_even_moments (hpos x) (hrange x) p).1)
    (fun x=>(secondScore_even_moments (hpos x) (hrange x) p).2)
  exact ⟨hi.1,hi.2.trans (integral_mul_const _ _)⟩

theorem firstScoreMoment_one : firstScoreMoment 1=1 := by
  simpa only [firstScoreMoment,show 2*1=2 by rfl,NNReal.coe_one] using gaussian_second_moment 1

end SHE.GaussianScoreKernel
