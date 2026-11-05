module

public import SHE.NativeGaussianFirstWord
public import SHE.GaussianCovarianceWordPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The explicit n=1 old-root/rough-leaf covariance comparison, using an
actual rank-one Gaussian law path and its centered covariance score. This
is a finite Gaussian marking statement, before continuum profile marking
and physical heat-tree integration. -/
namespace SHE.NativeGaussianCovarianceWord
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores NativeOldRoot
  GaussianCovarianceWord GaussianCovarianceWordPath GaussianRoughMoments ProfileL2
open scoped InnerProductSpace NNReal
variable {n:ℕ}

def firstWordCovarianceScore (A:Mat n) (D:State n) (v:ℝ≥0) (f a:ℝ→ℝ)
    (K L:State n→L[ℝ] ℝ) (m:State n):ℝ:=
  (1/2:ℝ)*∫y,centeredTest A (fun z=>oldRoot v f (K z)) (fun z=>a (L z)) m y*
    MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A

/-- The actual covariance mark includes the moving rough baseline and
retains the old Bernstein clipping and the centered rough Gaussian gain. -/
theorem firstWord_covariance_score_bound {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (v:ℝ≥0) (f f' a:ℝ→ℝ) (K L:State n→L[ℝ] ℝ) (A0 ν M H β:ℝ)
    (hA0:0≤A0) (hν:0≤ν) (hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0) (hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a) (haB:∀x,|a x|≤M) (hH:0≤H) (hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β) (m:State n):
    |firstWordCovarianceScore A D v f a K L m|≤
      2*A0*rootClipMass v ν*sqrt 2*scoreVariance A D*
        sqrt (H^2*Var[L;multivariateGaussian 0 A]^β*gaussianAbsMoment (2*β)):=by
  let μ:=multivariateGaussian (0:State n) A
  let b:State n→ℝ:=fun y=>oldRoot v f (K y)
  let aL:State n→ℝ:=fun y=>a (L y)
  let B:ℝ:=2*A0*rootClipMass v ν
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hbm:Measurable b:=(oldRoot_measurable v f hfc).comp K.continuous.measurable
  have ham:Measurable aL:=ha.comp L.continuous.measurable
  have hb:∀y,|b y|≤B:=fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (K y)
  have hab:∀y,|aL y|≤M:=fun _=>haB _
  have hL0:(∫y,L y ∂μ)=0:=by
    have hi:=L.integral_comp_comm (IsGaussian.integrable_id (μ:=μ))
    simpa only[μ,id_eq,integral_id_multivariateGaussian,map_zero] using hi
  have hh:=centered_holder_leaf_sq μ L hL0 a ha M H β haB hH hβ hholder (L m)
  have hs:normTwo μ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)^2≤
      H^2*Var[L;μ]^β*gaussianAbsMoment (2*β):=by
    simpa only[aL,GaussianCovarianceWord.average,map_add] using hh
  have hr:=sqrt_le_sqrt hs
  rw[Real.sqrt_sq (normTwo_nonneg _ _)] at hr
  have hc:=word_covariance_derivative_bound hA hD b aL hbm ham B M hb hab m
  exact hc.trans (mul_le_mul_of_nonneg_left hr (by
    dsimp only[B];exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0)
      (rootClipMass_nonneg v hν)) (sqrt_nonneg _)) (scoreVariance_nonneg hA hD)))

/-- The covariance derivative is of a genuine physical Gaussian family,
not an assumed score rule. Its residual is shared by product and baselines. -/
theorem exists_firstWord_covariance_derivative {A:Mat n} (hA:A.PosSemidef) {D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) (hV:0<scoreVariance A D)
    (v:ℝ≥0) (f f' a:ℝ→ℝ) (K L:State n→L[ℝ] ℝ) (A0 ν M:ℝ)
    (hA0:0≤A0) (hν:0≤ν) (hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0) (hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a) (haB:∀x,|a x|≤M) (m:State n):
    ∃η:Measure (State n), IsGaussian η ∧
      physicalCovarianceCurve A D η 0=multivariateGaussian 0 A ∧
      (∀(J:State n→L[ℝ] ℝ)(s:ℝ),0≤scoreVariance A D+s*scoreVariance A D^2→
        Var[J;physicalCovarianceCurve A D η s]=Var[J;multivariateGaussian 0 A]+s*(J D)^2) ∧
      HasDerivAt (fun s:ℝ=>measureWord (physicalCovarianceCurve A D η s)
        (fun y=>oldRoot v f (K y)) (fun y=>a (L y)) m)
        (firstWordCovarianceScore A D v f a K L m) 0:=by
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  exact exists_word_covariance_derivative hA hD hV
    (fun y=>oldRoot v f (K y)) (fun y=>a (L y))
    ((oldRoot_measurable v f hfc).comp K.continuous.measurable) (ha.comp L.continuous.measurable)
    (2*A0*rootClipMass v ν) M
    (fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (K y)) (fun _=>haB _) m

end SHE.NativeGaussianCovarianceWord
