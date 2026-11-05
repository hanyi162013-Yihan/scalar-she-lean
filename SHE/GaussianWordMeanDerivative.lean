module

public import SHE.GaussianWordFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The actual instantaneous mean derivative of the complete n=1 word.
This field can be evaluated along a changing covariance profile without
mistaking a fixed-covariance endpoint comparison for the full path. -/
namespace SHE.GaussianWordMeanDerivative
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianGramScore MeasurableGeneralizedInverse MeasurableGaussianScores NativeOldRoot
  GaussianCovarianceWord GaussianRoughMoments ProfileL2 GaussianScoreKernel
  NativeGaussianFirstWord GaussianWordFields
open scoped InnerProductSpace NNReal
variable {X:Type*}[MeasurableSpace X]{n:ℕ}

def firstMeanScore (A:Mat n)(D:State n)(v:ℝ≥0)(f a:ℝ→ℝ)
    (K L:State n→L[ℝ] ℝ)(m:State n):ℝ:=
  ∫y,centeredTest A (fun z=>oldRoot v f (K z)) (fun z=>a (L z)) m y*
    firstScore A D y ∂multivariateGaussian 0 A

theorem hasDerivAt_firstWord {A:Mat n}(hA:A.PosSemidef){D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (v:ℝ≥0)(f f' a:ℝ→ℝ)(K L:State n→L[ℝ] ℝ)(A0 ν M:ℝ)
    (hA0:0≤A0)(hν:0≤ν)(hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0)(hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a)(haB:∀x,|a x|≤M)(m:State n)(θ:ℝ):
    HasDerivAt (fun s:ℝ=>firstWord A v f a K L (m+s•D))
      (firstMeanScore A D v f a K L (m+θ•D)) θ:=by
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  exact hasDerivAt_word hA hD _ _
    ((oldRoot_measurable v f hfc).comp K.continuous.measurable) (ha.comp L.continuous.measurable)
    (2*A0*rootClipMass v ν) M
    (fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (K y)) (fun _=>haB _) m θ

theorem firstMeanScore_field_measurable (A:X→Mat n)(hA:Measurable A)
    (D m:X→State n)(hD:Measurable D)(hm:Measurable m)
    (v:ℝ≥0)(f a:ℝ→ℝ)(hf:Continuous f)(ha:Measurable a)(K L:State n→L[ℝ] ℝ):
    Measurable (fun x=>firstMeanScore (A x) (D x) v f a K L (m x)):=by
  let b:State n→ℝ:=fun z=>oldRoot v f (K z)
  let aL:State n→ℝ:=fun z=>a (L z)
  have hb:Measurable b:=(oldRoot_measurable v f hf).comp K.continuous.measurable
  have har:Measurable aL:=ha.comp L.continuous.measurable
  have hmb:=average_field_measurable A hA b hb m hm
  have hma:=average_field_measurable A hA aL har m hm
  have hshift:Measurable (fun p:X×State n=>m p.1+p.2):=(hm.comp measurable_fst).add measurable_snd
  have hcenter:Measurable (fun p:X×State n=>centeredTest (A p.1) b aL (m p.1) p.2):=
    (hb.comp hshift |>.sub (hmb.comp measurable_fst)).mul
      (har.comp hshift |>.sub (hma.comp measurable_fst))
  have hscore:Measurable (fun p:X×State n=>firstScore (A p.1) (D p.1) p.2):=by
    convert! (firstScore_measurable (n:=n)).comp
      (((hA.prodMk hD).comp (measurable_fst:Measurable (Prod.fst:X×State n→X))).prodMk measurable_snd) using 1
  exact ((hcenter.mul hscore).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=gaussianKernel A hA)).measurable

/-- Pointwise physical score bound for the actual full word derivative,
including its baseline. The only rough leaf gain is proved from moments. -/
theorem firstMeanScore_bound {A:Mat n}(hA:A.PosSemidef){D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (v:ℝ≥0)(f f' a:ℝ→ℝ)(K L:State n→L[ℝ] ℝ)(A0 ν M H β W:ℝ)
    (hA0:0≤A0)(hν:0≤ν)(hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0)(hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a)(haB:∀x,|a x|≤M)(hH:0≤H)(hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β)
    (hW:Var[L;multivariateGaussian 0 A]≤W)(m:State n):
    |firstMeanScore A D v f a K L m|≤
      (4*A0*rootClipMass v ν*sqrt (H^2*W^β*gaussianAbsMoment (2*β)))*sqrt (scoreVariance A D):=by
  let μ:=multivariateGaussian (0:State n) A
  let b:State n→ℝ:=fun y=>oldRoot v f (K y)
  let aL:State n→ℝ:=fun y=>a (L y)
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hL0:(∫y,L y ∂μ)=0:=by
    have hi:=L.integral_comp_comm (IsGaussian.integrable_id (μ:=μ))
    simpa only[μ,id_eq,integral_id_multivariateGaussian,map_zero] using hi
  have hh:=centered_holder_leaf_sq μ L hL0 a ha M H β haB hH hβ hholder (L m)
  have hR:normTwo μ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)≤
      sqrt (H^2*W^β*gaussianAbsMoment (2*β)):=by
    have hs:normTwo μ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)^2≤
        H^2*W^β*gaussianAbsMoment (2*β):=by
      have hh':normTwo μ (fun y=>aL (m+y)-GaussianCovarianceWord.average A aL m)^2≤
          H^2*Var[L;μ]^β*gaussianAbsMoment (2*β):=by
        simpa only[aL,GaussianCovarianceWord.average,map_add] using hh
      exact hh'.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (rpow_le_rpow (variance_nonneg _ _) hW hβ) (sq_nonneg _))
          (gaussianAbsMoment_nonneg _))
    have hsqrt:=sqrt_le_sqrt hs
    rwa[Real.sqrt_sq (normTwo_nonneg _ _)] at hsqrt
  have hc:=word_mean_derivative_bound hA hD b aL
    ((oldRoot_measurable v f hfc).comp K.continuous.measurable) (ha.comp L.continuous.measurable)
    (2*A0*rootClipMass v ν) M
    (fun y=>oldRoot_clipped_bound v f f' hA0 hν hf hfb hfD (K y)) (fun _=>haB _) m
  have hm:=mul_le_mul_of_nonneg_left hR
    (show 0≤2*(2*A0*rootClipMass v ν)*sqrt (scoreVariance A D) by positivity [rootClipMass_nonneg v hν])
  convert! hc.trans hm using 1
  ring

/-- Integrability and square-energy transfer for the instantaneous word
mean mark, allowing arbitrary dependence and rank changes in its fields. -/
theorem firstMeanScore_square_integral (μ:Measure X)
    (A:X→Mat n)(hA:Measurable A)(hpos:∀x,(A x).PosSemidef)
    (D m:X→State n)(hD:Measurable D)(hm:Measurable m)
    (hrange:∀x,D x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A x)).range)
    (hV:Integrable (fun x=>scoreVariance (A x) (D x)) μ)
    (v:ℝ≥0)(f f' a:ℝ→ℝ)(K L:State n→L[ℝ] ℝ)(A0 ν M H β W:ℝ)
    (hA0:0≤A0)(hν:0≤ν)(hf:∀x,HasDerivAt f (f' x) x)
    (hfb:∀x,|f x|≤A0)(hfD:∀x,|f' x|≤A0*ν)
    (ha:Measurable a)(haB:∀x,|a x|≤M)(hH:0≤H)(hβ:0≤β)
    (hholder:∀x z,|a x-a z|≤H*|x-z|^β)(hW:∀x,Var[L;multivariateGaussian 0 (A x)]≤W):
    let T:=4*A0*rootClipMass v ν*sqrt (H^2*W^β*gaussianAbsMoment (2*β))
    Integrable (fun x=>firstMeanScore (A x) (D x) v f a K L (m x)^2) μ ∧
      (∫x,firstMeanScore (A x) (D x) v f a K L (m x)^2 ∂μ)≤T^2*(∫x,scoreVariance (A x) (D x) ∂μ):=by
  intro T
  let F:=fun x=>firstMeanScore (A x) (D x) v f a K L (m x)
  have hfc:Continuous f:=continuous_iff_continuousAt.mpr (fun x=>(hf x).continuousAt)
  have hFm:Measurable F:=firstMeanScore_field_measurable A hA D m hD hm v f a hfc ha K L
  have hb (x:X):F x^2≤T^2*scoreVariance (A x) (D x):=by
    have hc:=firstMeanScore_bound (hpos x) (hrange x) v f f' a K L A0 ν M H β W
      hA0 hν hf hfb hfD ha haB hH hβ hholder (hW x) (m x)
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hc 2
    simpa only[F,T,sq_abs,mul_pow,sq_sqrt (scoreVariance_nonneg (hpos x) (hrange x))] using hh
  have hi:Integrable (fun x=>F x^2) μ:=(hV.const_mul (T^2)).mono'
    (hFm.pow_const 2).aestronglyMeasurable (ae_of_all _ (fun x=>by
      rw[Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (F x))];exact hb x))
  exact ⟨hi,(integral_mono hi (hV.const_mul _) hb).trans_eq (integral_const_mul _ _)⟩

end SHE.GaussianWordMeanDerivative
