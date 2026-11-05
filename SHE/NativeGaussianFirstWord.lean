module

public import SHE.NativeOldRoot
public import SHE.GaussianCovarianceWord
public import SHE.GaussianRoughMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! An explicit n=1 Gaussian comparison: the fixed old second-score fraction
acts only on the root, while a whole future Gaussian reserve observes both
root and newest rough leaf. Its deterministic rough baseline follows the
same mean path. The covariance is fixed in this mean/baseline leg; covariance
profile marking and the physical heat-tree/time assembly are separate. -/
namespace SHE.NativeGaussianFirstWord
open Set MeasureTheory ProbabilityTheory Real GaussianAudit GaussianIncrement
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores NativeOldRoot
  GaussianCovarianceWord GaussianRoughMoments ProfileL2
open scoped NNReal InnerProductSpace
variable {n:ℕ}

def firstWord (A:Mat n) (v:ℝ≥0) (f a:ℝ→ℝ) (K L:State n→L[ℝ] ℝ) (m:State n):ℝ:=
  word A (fun y=>oldRoot v f (K y)) (fun y=>a (L y)) m

/-- The actual centered n=1 word has a clipped mean comparison, with the
old Bernstein clip and the sole new physical Gaussian mean energy. All
Gaussian projections may be correlated and the covariance may be singular. -/
theorem firstWord_mean_comparison {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (v:ℝ≥0) (f f' a:ℝ→ℝ) (K L:State n→L[ℝ] ℝ) (A0 ν M H β:ℝ)
    (hA0:0≤A0) (hν:0≤ν) (hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0) (hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a) (haB:∀x,|a x|≤M) (hH:0≤H) (hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β) (m:State n):
    |firstWord A v f a K L (m+D)-firstWord A v f a K L m|≤
      4*A0*rootClipMass v ν * sqrt (H^2*Var[L;multivariateGaussian 0 A]^β*gaussianAbsMoment (2*β)) *
        min 1 (sqrt (scoreVariance A D)):=by
  let μ:=multivariateGaussian (0:State n) A
  let b:State n→ℝ:=fun y=>oldRoot v f (K y)
  let aL:State n→ℝ:=fun y=>a (L y)
  let B:ℝ:=2*A0*rootClipMass v ν
  let R:ℝ:=H^2*Var[L;μ]^β*gaussianAbsMoment (2*β)
  have hB0:0≤B:=mul_nonneg (mul_nonneg (by norm_num) hA0) (rootClipMass_nonneg v hν)
  have hR:0≤R:=mul_nonneg (mul_nonneg (sq_nonneg _) (rpow_nonneg (variance_nonneg L μ) _))
    (gaussianAbsMoment_nonneg _)
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hbm:Measurable b:=(oldRoot_measurable v f hfc).comp K.continuous.measurable
  have ham:Measurable aL:=ha.comp L.continuous.measurable
  have hb:∀y,|b y|≤B:=fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (K y)
  have hab:∀y,|aL y|≤M:=fun y=>haB _
  have hL0:(∫y,L y ∂μ)=0:=by
    have hi:=L.integral_comp_comm (IsGaussian.integrable_id (μ:=μ))
    simpa only[μ,id_eq,integral_id_multivariateGaussian,map_zero] using hi
  have hrough (m':State n):normTwo μ (fun y=>aL (m'+y)-GaussianCovarianceWord.average A aL m')≤sqrt R:=by
    have hh:=centered_holder_leaf_sq μ L hL0 a ha M H β haB hH hβ hholder (L m')
    have hs:normTwo μ (fun y=>aL (m'+y)-GaussianCovarianceWord.average A aL m')^2≤R:=by
      simpa only[aL,GaussianCovarianceWord.average,map_add,μ,R] using hh
    have hr:=sqrt_le_sqrt hs
    rw[Real.sqrt_sq (normTwo_nonneg _ _)] at hr
    exact hr
  have hder (θ:ℝ):HasDerivAt (fun s:ℝ=>word A b aL (m+s•D))
      (∫y,centeredTest A b aL (m+θ•D) y*firstScore A D y ∂μ) θ:=
    hasDerivAt_word hA hD b aL hbm ham B M hb hab m θ
  have hderbound (θ:ℝ):|∫y,centeredTest A b aL (m+θ•D) y*firstScore A D y ∂μ|≤
      2*B*sqrt (scoreVariance A D)*sqrt R:=
    (word_mean_derivative_bound hA hD b aL hbm ham B M hb hab (m+θ•D)).trans
      (mul_le_mul_of_nonneg_left (hrough _) (by positivity))
  have hlinear:|word A b aL (m+D)-word A b aL m|≤2*B*sqrt (scoreVariance A D)*sqrt R:=by
    have hm:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s:=Set.univ)
      (f:=fun s:ℝ=>word A b aL (m+s•D))
      (f':=fun θ:ℝ=>∫y,centeredTest A b aL (m+θ•D) y*firstScore A D y ∂μ)
      (C:=2*B*sqrt (scoreVariance A D)*sqrt R) (fun θ _=>(hder θ).hasDerivWithinAt)
      (fun θ _=>by simpa only[Real.norm_eq_abs] using hderbound θ)
      convex_univ (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
    simpa only[zero_smul,add_zero,one_smul,Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hm
  have hamp:|word A b aL (m+D)-word A b aL m|≤2*B*sqrt R:=by
    have h0:|word A b aL m|≤B*sqrt R:=(word_amplitude_bound A b aL hbm ham B M hb hab m).trans
      (mul_le_mul_of_nonneg_left (hrough m) hB0)
    have h1:|word A b aL (m+D)|≤B*sqrt R:=(word_amplitude_bound A b aL hbm ham B M hb hab (m+D)).trans
      (mul_le_mul_of_nonneg_left (hrough (m+D)) hB0)
    exact (abs_sub _ _).trans (by linarith)
  change |word A b aL (m+D)-word A b aL m|≤_
  by_cases hc:sqrt (scoreVariance A D)≤1
  · rw[min_eq_right hc]
    convert! hlinear using 1
    dsimp only[B,R,μ]
    ring
  · rw[min_eq_left (le_of_not_ge hc),mul_one]
    convert! hamp using 1
    dsimp only[B,R,μ]
    ring

/-- The old root mass is itself controlled by its exact scalar Gaussian
variance; no centered increment estimate is left as a premise. -/
theorem firstWord_mean_comparison_scaled {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    {v:ℝ≥0} (hv:v≠0) (f f' a:ℝ→ℝ) (K L:State n→L[ℝ] ℝ) (A0 ν M H β:ℝ)
    (hA0:0≤A0) (hν:0≤ν) (hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0) (hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a) (haB:∀x,|a x|≤M) (hH:0≤H) (hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β) (m:State n):
    |firstWord A v f a K L (m+D)-firstWord A v f a K L m|≤
      (4*A0*rootClipConstant/(v:ℝ))*min 1 (ν*sqrt (v:ℝ)) *
        sqrt (H^2*Var[L;multivariateGaussian 0 A]^β*gaussianAbsMoment (2*β)) *
          min 1 (sqrt (scoreVariance A D)):=by
  have h:=firstWord_mean_comparison hA hD v f f' a K L A0 ν M H β hA0 hν hf hfb hfD ha haB hH hβ hholder m
  apply h.trans
  have hh:=mul_le_mul_of_nonneg_left (rootClipMass_scaled_bound hv hν) (show 0≤4*A0 by positivity)
  have hm:=mul_le_mul_of_nonneg_right hh (sqrt_nonneg (H^2*Var[L;multivariateGaussian 0 A]^β*gaussianAbsMoment (2*β)))
  have hc:0≤min (1:ℝ) (sqrt (scoreVariance A D)):=le_min (by norm_num) (sqrt_nonneg _)
  have hf:=mul_le_mul_of_nonneg_right hm hc
  convert! hf using 1; ring

end SHE.NativeGaussianFirstWord
