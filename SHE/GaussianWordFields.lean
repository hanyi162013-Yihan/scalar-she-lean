module

public import SHE.NativeGaussianFirstWord
public import SHE.GaussianScoreKernel
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Actual parameter-dependent bounded Gaussian first words and their
one-input square-energy estimate. The covariance, mean, and signed direction
may all depend on the same parameter, with arbitrary rank changes. -/
namespace SHE.GaussianWordFields
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores NativeOldRoot
  GaussianCovarianceWord GaussianRoughMoments ProfileL2 GaussianScoreKernel
  NativeGaussianFirstWord
open scoped InnerProductSpace NNReal
variable {X:Type*} [MeasurableSpace X] {n:ℕ}

theorem average_field_measurable (A:X→Mat n) (hA:Measurable A)
    (f:State n→ℝ) (hf:Measurable f) (m:X→State n) (hm:Measurable m):
    Measurable (fun x=>GaussianCovarianceWord.average (A x) f (m x)):=by
  have hs:Measurable (fun p:X×State n=>f (m p.1+p.2)):=
    hf.comp ((hm.comp measurable_fst).add measurable_snd)
  exact (hs.stronglyMeasurable.integral_kernel_prod_right' (κ:=gaussianKernel A hA)).measurable

theorem firstWord_field_measurable (A:X→Mat n) (hA:Measurable A)
    (v:ℝ≥0) (f a:ℝ→ℝ) (hf:Continuous f) (ha:Measurable a)
    (K L:State n→L[ℝ] ℝ) (m:X→State n) (hm:Measurable m):
    Measurable (fun x=>firstWord (A x) v f a K L (m x)):=by
  have hb:Measurable (fun y:State n=>oldRoot v f (K y)):=
    (oldRoot_measurable v f hf).comp K.continuous.measurable
  have har:Measurable (fun y:State n=>a (L y)):=ha.comp L.continuous.measurable
  exact (average_field_measurable A hA _ (hb.mul har) m hm).sub
    ((average_field_measurable A hA _ hb m hm).mul (average_field_measurable A hA _ har m hm))

/-- A literal Gaussian word, rather than an unspecified kernel amplitude,
has square energy controlled by its actual physical mean-score energy.
No independence of the parameter, covariance, centers, or input is used. -/
theorem firstWord_mean_square_integral (μ:Measure X)
    (A:X→Mat n) (hA:Measurable A) (hpos:∀x,(A x).PosSemidef)
    (D m:X→State n) (hD:Measurable D) (hm:Measurable m)
    (hrange:∀x,D x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A x)).range)
    (hV:Integrable (fun x=>scoreVariance (A x) (D x)) μ)
    (v:ℝ≥0) (f f' a:ℝ→ℝ) (K L:State n→L[ℝ] ℝ) (A0 ν M H β W:ℝ)
    (hA0:0≤A0) (hν:0≤ν) (hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0) (hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a) (haB:∀x,|a x|≤M) (hH:0≤H) (hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β)
    (hW:∀x,Var[L;multivariateGaussian 0 (A x)]≤W):
    let T:=4*A0*rootClipMass v ν*sqrt (H^2*W^β*gaussianAbsMoment (2*β))
    Integrable (fun x=>(firstWord (A x) v f a K L (m x+D x)-firstWord (A x) v f a K L (m x))^2) μ ∧
      (∫x,(firstWord (A x) v f a K L (m x+D x)-firstWord (A x) v f a K L (m x))^2 ∂μ)≤
        T^2*(∫x,scoreVariance (A x) (D x) ∂μ):=by
  intro T
  let F:X→ℝ:=fun x=>firstWord (A x) v f a K L (m x+D x)-firstWord (A x) v f a K L (m x)
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hFm:Measurable F:=
    (firstWord_field_measurable A hA v f a hfc ha K L _ (hm.add hD)).sub
      (firstWord_field_measurable A hA v f a hfc ha K L m hm)
  have hT0:0≤T:=by dsimp[T];positivity [rootClipMass_nonneg v hν]
  have hb (x:X):F x^2≤T^2*scoreVariance (A x) (D x):=by
    have hc:=firstWord_mean_comparison (hpos x) (hrange x) v f f' a K L A0 ν M H β
      hA0 hν hf hfb hfD ha haB hH hβ hholder (m x)
    have hR:sqrt (H^2*Var[L;multivariateGaussian 0 (A x)]^β*gaussianAbsMoment (2*β))≤
        sqrt (H^2*W^β*gaussianAbsMoment (2*β)):=by
      apply sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rpow_le_rpow (variance_nonneg _ _) (hW x) hβ) (sq_nonneg _))
        (gaussianAbsMoment_nonneg _)
    have hlin:|F x|≤T*sqrt (scoreVariance (A x) (D x)):=by
      calc
        _≤_:=hc
        _≤T*min 1 (sqrt (scoreVariance (A x) (D x))):=by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR (by positivity [rootClipMass_nonneg v hν]))
            (le_min (by norm_num) (sqrt_nonneg _))
        _≤_:=mul_le_mul_of_nonneg_left (min_le_right _ _) hT0
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hlin 2
    simpa only[sq_abs,mul_pow,sq_sqrt (scoreVariance_nonneg (hpos x) (hrange x))] using hh
  have hi:Integrable (fun x=>F x^2) μ:=(hV.const_mul (T^2)).mono'
    (hFm.pow_const 2).aestronglyMeasurable (ae_of_all _ (fun x=>by rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)];exact hb x))
  refine ⟨hi,?_⟩
  calc
    _≤∫x,T^2*scoreVariance (A x) (D x) ∂μ:=integral_mono hi (hV.const_mul _) hb
    _=_:=integral_const_mul _ _

end SHE.GaussianWordFields
