module

public import SHE.GaussianWordAffine
public import SHE.NativeGaussianCovarianceWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The continuum covariance derivative retains one literal signed input
inside its positive canonical score-energy kernel. No product of unbounded
inputs and no independence of the old root and rough leaf is used. -/
namespace SHE.GaussianWordCovarianceBound
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianProfileMark
  GaussianRangeSmooth GaussianConvolution GaussianCovarianceWord GaussianWordAffine
  GaussianWordCovarianceIntegral MeasurableGaussianScores GaussianCovarianceWordPath
  GaussianAudit NativeOldRoot NativeGaussianCovarianceWord GaussianRoughMoments ProfileL2
open scoped NNReal InnerProductSpace
variable {n:ℕ}{X:Type*}[MeasurableSpace X]

theorem centeredMark_outer_integrable (μ:Measure X){A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)
    (v:X→State n)(hv:Measurable v)(hrange:∀ᵐx ∂μ,v x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (e:X→ℝ)(he:Measurable e)(henergy:Integrable (fun x=>|e x| *‖v x‖^2) μ)
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(z:State n):
    Integrable (fun x=>e x*(∫y,centeredTest A b a z y*secondScore A (v x) y
      ∂multivariateGaussian 0 A)) μ:=by
  have hib:=rawMark_outer_integrable μ hA v hv hrange e he henergy b hb B hB z
  have hia:=rawMark_outer_integrable μ hA v hv hrange e he henergy a ha M hM z
  have hip:=rawMark_outer_integrable μ hA v hv hrange e he henergy (fun y=>b y*a y) (hb.mul ha) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0))) z
  apply ((hip.sub (hib.mul_const (GaussianCovarianceWord.average A a z))).sub
    (hia.const_mul (GaussianCovarianceWord.average A b z))).congr
  filter_upwards[hrange] with x hx
  rw[centered_second_score_identity hA hx b a hb ha B M hB hM z]
  change e x*rawMark A (fun y=>b y*a y) z (v x)-
      e x*rawMark A b z (v x)*GaussianCovarianceWord.average A a z-
      GaussianCovarianceWord.average A b z*(e x*rawMark A a z (v x))=_
  unfold rawMark
  ring

theorem scoreEnergy_outer_integrable (μ:Measure X)(A:Matrix (Fin n) (Fin n) ℝ)
    (v:X→State n)(hv:Measurable v)(e:X→ℝ)(he:Measurable e)
    (henergy:Integrable (fun x=>|e x| *‖v x‖^2) μ):
    Integrable (fun x=>|e x| *scoreVariance A (v x)) μ:=by
  apply (henergy.const_mul ‖(MeasurableGeneralizedInverse.generalizedInverse A).toContinuousLinearMap‖).mono'
    (((continuous_abs.measurable.comp he).mul
      (scoreVariance_measurable.comp (measurable_const.prodMk hv))).aestronglyMeasurable)
  filter_upwards with x
  change ‖|e x| *scoreVariance A (v x)‖≤_
  rw[Real.norm_eq_abs,abs_mul,abs_abs]
  convert! mul_le_mul_of_nonneg_left (scoreVariance_coarse_bound A (v x)) (abs_nonneg (e x)) using 1
  ring

/-- Exact positive-kernel bound for the complete centered continuum mark,
including both baseline derivatives. The physical input remains unsquared. -/
theorem covarianceMark_bound (μ:Measure X){A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)
    (v:X→State n)(hv:Measurable v)(hrange:∀ᵐx ∂μ,v x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (e:X→ℝ)(he:Measurable e)(henergy:Integrable (fun x=>|e x| *‖v x‖^2) μ)
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(z:State n):
    |covarianceMark μ A e v b a z|≤B*sqrt 2*
      normTwo (multivariateGaussian 0 A) (fun y=>a (z+y)-GaussianCovarianceWord.average A a z)*
      (∫x,|e x| *scoreVariance A (v x) ∂μ):=by
  let R:=normTwo (multivariateGaussian 0 A) (fun y=>a (z+y)-GaussianCovarianceWord.average A a z)
  let T:=B*sqrt 2*R
  have hi:=centeredMark_outer_integrable μ hA v hv hrange e he henergy b a hb ha B M hB hM z
  have hV:=scoreEnergy_outer_integrable μ A v hv e he henergy
  have hT:0≤T:=mul_nonneg (mul_nonneg ((abs_nonneg (b 0)).trans (hB 0)) (sqrt_nonneg _)) (normTwo_nonneg _ _)
  unfold covarianceMark
  rw[←integral_const_mul,←Real.norm_eq_abs]
  calc
    _≤∫x,‖(1/2:ℝ)*(e x*(∫y,centeredTest A b a z y*secondScore A (v x) y ∂multivariateGaussian 0 A))‖ ∂μ:=
      norm_integral_le_integral_norm _
    _≤∫x,T*(|e x| *scoreVariance A (v x)) ∂μ:=by
      apply integral_mono_ae (hi.const_mul (1/2:ℝ)).norm (hV.const_mul T)
      filter_upwards[hrange] with x hx
      have hh:=word_covariance_derivative_bound hA hx b a hb ha B M hB hM z
      change ‖(1/2:ℝ)*(e x*_)‖≤T*(|e x| *scoreVariance A (v x))
      rw[Real.norm_eq_abs]
      have heq (w:ℝ):(1/2:ℝ)*(e x*w)=e x*((1/2:ℝ)*w):=by ring
      rw[heq,abs_mul]
      convert! mul_le_mul_of_nonneg_left hh (abs_nonneg (e x)) using 1
      dsimp[T,R];ring
    _=T*(∫x,|e x| *scoreVariance A (v x) ∂μ):=integral_const_mul _ _

/-- The actual old scalar second score and the centered rough Gaussian
gain remain intact through the signed continuum covariance integral. -/
theorem firstWord_covarianceMark_bound (μ:Measure X){A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)
    (row:X→State n)(hrow:Measurable row)
    (hrange:∀ᵐx ∂μ,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (e:X→ℝ)(he:Measurable e)(henergy:Integrable (fun x=>|e x| *‖row x‖^2) μ)
    (v:ℝ≥0)(f f' a:ℝ→ℝ)(K L:State n→L[ℝ] ℝ)(A0 ν M H β W:ℝ)
    (hA0:0≤A0)(hν:0≤ν)(hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0)(hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a)(haB:∀x,|a x|≤M)(hH:0≤H)(hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β)
    (hW:Var[L;multivariateGaussian 0 A]≤W)(m:State n):
    |covarianceMark μ A e row (fun y=>oldRoot v f (K y)) (fun y=>a (L y)) m|≤
      2*A0*rootClipMass v ν*sqrt 2*sqrt (H^2*W^β*gaussianAbsMoment (2*β))*
        (∫x,|e x| *scoreVariance A (row x) ∂μ):=by
  let γ:=multivariateGaussian (0:State n) A
  let b:=fun y:State n=>oldRoot v f (K y)
  let aL:=fun y:State n=>a (L y)
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hb:Measurable b:=(oldRoot_measurable v f hfc).comp K.continuous.measurable
  have ham:Measurable aL:=ha.comp L.continuous.measurable
  have hbb:∀y,|b y|≤2*A0*rootClipMass v ν:=
    fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (K y)
  have hL0:(∫y,L y ∂γ)=0:=by
    have hi:=L.integral_comp_comm (IsGaussian.integrable_id (μ:=γ))
    simpa only[γ,id_eq,integral_id_multivariateGaussian,map_zero] using hi
  have hh:=centered_holder_leaf_sq γ L hL0 a ha M H β haB hH hβ hholder (L m)
  have hR:normTwo γ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)≤
      sqrt (H^2*W^β*gaussianAbsMoment (2*β)):=by
    have hs:normTwo γ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)^2≤
        H^2*W^β*gaussianAbsMoment (2*β):=by
      have hh':normTwo γ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)^2≤
          H^2*Var[L;γ]^β*gaussianAbsMoment (2*β):=by
        simpa only[aL,GaussianCovarianceWord.average,map_add] using hh
      exact hh'.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rpow_le_rpow (variance_nonneg _ _) hW hβ) (sq_nonneg _))
        (gaussianAbsMoment_nonneg _))
    have hr:=sqrt_le_sqrt hs
    rwa[Real.sqrt_sq (normTwo_nonneg _ _)] at hr
  have hI:0≤(∫x,|e x| *scoreVariance A (row x) ∂μ):=by
    apply integral_nonneg_of_ae
    filter_upwards[hrange] with x hx
    exact mul_nonneg (abs_nonneg _) (scoreVariance_nonneg hA hx)
  have hbnd:=covarianceMark_bound μ hA row hrow hrange e he henergy b aL hb ham
    (2*A0*rootClipMass v ν) M hbb (fun _=>haB _) m
  exact hbnd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR (by positivity [rootClipMass_nonneg v hν])) hI)

end SHE.GaussianWordCovarianceBound
