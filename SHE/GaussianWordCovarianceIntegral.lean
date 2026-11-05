module

public import SHE.GaussianCovarianceWordPath
public import SHE.GaussianUniformFloor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Genuine integrability and centering of continuum covariance marks for
the complete bounded root/rough word. A coarse finite inverse norm is used
only to justify the outer integrals; the actual score energy is retained
in the sharp pointwise estimate. -/
namespace SHE.GaussianWordCovarianceIntegral
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit GaussianGramScore
  MeasurableGeneralizedInverse MeasurableGaussianScores GaussianCovarianceWord
  GaussianCovarianceWordPath GaussianProfileMark GaussianRangeSmooth GaussianConvolution ProfileL2
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {n:ℕ}{X:Type*}[MeasurableSpace X]

def rawMark (A:Matrix (Fin n) (Fin n) ℝ)(F:State n→ℝ)(z D:State n):ℝ:=
  ∫y,F (z+y)*MeasurableGaussianScores.secondScore A D y ∂multivariateGaussian 0 A

theorem rawMark_measurable (A:Matrix (Fin n) (Fin n) ℝ)(F:State n→ℝ)(hF:Measurable F)(z:State n):
    Measurable (rawMark A F z):=by
  have hS:Measurable (fun p:State n×State n=>MeasurableGaussianScores.secondScore A p.1 p.2):=by
    convert! (secondScore_measurable (n:=n)).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd) using 1
  exact (((hF.comp (measurable_const.add measurable_snd)).mul hS).stronglyMeasurable.integral_prod_right').measurable

theorem rawMark_bound {A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef){D:State n}
    (hD:D∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)(F:State n→ℝ)(hF:Measurable F)
    (M:ℝ)(hM:∀y,|F y|≤M)(z:State n):
    |rawMark A F z D|≤M*sqrt 2*scoreVariance A D:=by
  have hM0:0≤M:=(abs_nonneg (F 0)).trans (hM 0)
  have hf:MemLp (fun y=>F (z+y)) 2 (multivariateGaussian 0 A):=bounded_memLp (by fun_prop) (fun _=>hM _)
  have hs:MemLp (MeasurableGaussianScores.secondScore A D) 2 (multivariateGaussian 0 A):=by
    apply (memLp_two_iff_integrable_sq
      (by unfold MeasurableGaussianScores.secondScore MeasurableGaussianScores.firstScore;fun_prop)).mpr
    simpa only[show 2*1=2 by rfl,sq_abs] using (secondScore_even_moments hA hD 1).1
  have hnorm:normTwo (multivariateGaussian 0 A) (MeasurableGaussianScores.secondScore A D)=sqrt 2*scoreVariance A D:=by
    have he:=(secondScore_even_moments hA hD 1).2
    simp only[show 2*1=2 by rfl,GaussianCovarianceWordPath.secondScoreMoment_one,sq_abs] at he
    unfold normTwo
    rw[he,sqrt_mul (sq_nonneg _),sqrt_sq (scoreVariance_nonneg hA hD)]
    ring
  have hc:=integral_mul_normTwo_bound hf hs
  rw[hnorm] at hc
  have hb:=normTwo_bound (μ:=multivariateGaussian 0 A) (f:=fun y=>F (z+y)) (by fun_prop) hM0 (fun _=>hM _)
  convert! hc.trans (mul_le_mul_of_nonneg_right hb (mul_nonneg (sqrt_nonneg _) (scoreVariance_nonneg hA hD))) using 1
  ring

theorem scoreVariance_coarse_bound (A:Matrix (Fin n) (Fin n) ℝ)(D:State n):
    |scoreVariance A D|≤‖(generalizedInverse A).toContinuousLinearMap‖*‖D‖^2:=by
  have hi:=norm_inner_le_norm (𝕜:=ℝ) (coefficient A D) D
  have hn:‖coefficient A D‖≤‖(generalizedInverse A).toContinuousLinearMap‖*‖D‖:=
    (generalizedInverse A).toContinuousLinearMap.le_opNorm D
  change |inner ℝ (coefficient A D) D|≤_
  rw[←Real.norm_eq_abs]
  exact hi.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (by ring))

/-- Continuum raw score marks are integrable under the actual physical
frame-energy dominator, with no independence or test smoothness premise. -/
theorem rawMark_outer_integrable (μ:Measure X){A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)
    (v:X→State n)(hv:Measurable v)(hrange:∀ᵐx ∂μ,v x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (e:X→ℝ)(he:Measurable e)(henergy:Integrable (fun x=>|e x| *‖v x‖^2) μ)
    (F:State n→ℝ)(hF:Measurable F)(M:ℝ)(hM:∀y,|F y|≤M)(z:State n):
    Integrable (fun x=>e x*rawMark A F z (v x)) μ:=by
  let K:=‖(generalizedInverse A).toContinuousLinearMap‖
  have hM0:0≤M:=(abs_nonneg (F 0)).trans (hM 0)
  apply (henergy.const_mul (M*sqrt 2*K)).mono'
    (he.mul ((rawMark_measurable A F hF z).comp hv)).aestronglyMeasurable
  filter_upwards[hrange] with x hx
  change ‖e x*rawMark A F z (v x)‖≤_
  rw[Real.norm_eq_abs,abs_mul]
  have hb:|rawMark A F z (v x)|≤(M*sqrt 2*K)*‖v x‖^2:=by
    have hh:=rawMark_bound hA hx F hF M hM z
    have hvb:=scoreVariance_coarse_bound A (v x)
    rw[abs_of_nonneg (scoreVariance_nonneg hA hx)] at hvb
    convert! hh.trans (mul_le_mul_of_nonneg_left hvb (mul_nonneg hM0 (sqrt_nonneg _))) using 1
    ring
  convert! mul_le_mul_of_nonneg_left hb (abs_nonneg (e x)) using 1
  ring

/-- Exact centered outer mark: all baseline terms combine inside the same
physical continuum covariance integral. -/
theorem outer_centered_identity (μ:Measure X){A:Matrix (Fin n) (Fin n) ℝ}(hA:A.PosSemidef)
    (v:X→State n)(hv:Measurable v)(hrange:∀ᵐx ∂μ,v x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (e:X→ℝ)(he:Measurable e)(henergy:Integrable (fun x=>|e x| *‖v x‖^2) μ)
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(z:State n):
    (∫x,e x*(∫y,centeredTest A b a z y*MeasurableGaussianScores.secondScore A (v x) y ∂multivariateGaussian 0 A) ∂μ)=
      (∫x,e x*rawMark A (fun y=>b y*a y) z (v x) ∂μ)-
      (∫x,e x*rawMark A b z (v x) ∂μ)*GaussianCovarianceWord.average A a z-
      GaussianCovarianceWord.average A b z*(∫x,e x*rawMark A a z (v x) ∂μ):=by
  have hib:=rawMark_outer_integrable μ hA v hv hrange e he henergy b hb B hB z
  have hia:=rawMark_outer_integrable μ hA v hv hrange e he henergy a ha M hM z
  have hip:=rawMark_outer_integrable μ hA v hv hrange e he henergy (fun y=>b y*a y) (hb.mul ha) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0))) z
  calc
    _=∫x,(e x*rawMark A (fun y=>b y*a y) z (v x)-
        (e x*rawMark A b z (v x))*GaussianCovarianceWord.average A a z)-
        GaussianCovarianceWord.average A b z*(e x*rawMark A a z (v x)) ∂μ:=by
      apply integral_congr_ae
      filter_upwards[hrange] with x hx
      rw[centered_second_score_identity hA hx b a hb ha B M hB hM z]
      unfold rawMark
      ring
    _=_:=by
      have his:Integrable (fun x=>e x*rawMark A (fun y=>b y*a y) z (v x)-
        e x*rawMark A b z (v x)*GaussianCovarianceWord.average A a z) μ:=
        hip.sub (hib.mul_const _)
      rw[integral_sub his (hia.const_mul _)]
      rw[integral_sub hip (hib.mul_const _),integral_mul_const,integral_const_mul]


/-- Every actual physical frame row lies almost everywhere in its weighted
covariance range when the scalar weight has a positive floor. -/
theorem ae_frame_mem_profile_range (μ:Measure X)(v:X→State n)
    (hv:AEStronglyMeasurable v μ)(henergy:Integrable (fun x=>‖v x‖^2) μ)
    (c:X→ℝ)(hc:AEStronglyMeasurable c μ)(hci:Integrable (fun x=>|c x| *‖v x‖^2) μ)
    {ell:ℝ}(hell:0<ell)(hclower:∀ᵐx ∂μ,ell≤c x):
    ∀ᵐx ∂μ,v x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariance μ c v)).range:=by
  let k:X→ℝ:=fun x=>c x-ell
  have hkm:AEStronglyMeasurable k μ:=hc.sub aestronglyMeasurable_const
  have hki:Integrable (fun x=>|k x| *‖v x‖^2) μ:=by
    apply (hci.add (henergy.const_mul |ell|)).mono' (hkm.norm.mul (hv.norm.pow 2))
    filter_upwards with x
    rw[Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (abs_sub (c x) ell) (sq_nonneg _)).trans_eq (by simp only[Pi.add_apply];ring)
  have hiG:=profileCovariance_integrable μ (fun _=>1) v aestronglyMeasurable_const hv
    (by simpa only[abs_one,one_mul] using henergy)
  have hiK:=profileCovariance_integrable μ k v hkm hv hki
  have hG: (profileCovariance μ (fun _=>1) v).PosSemidef:=
    profileCovariance_positive μ (fun _=>1) v hiG (ae_of_all _ (by norm_num))
  have hK: (profileCovariance μ k v).PosSemidef:=
    profileCovariance_positive μ k v hiK (hclower.mono (fun x hx=>sub_nonneg.mpr hx))
  have he:profileCovariance μ c v=ell•profileCovariance μ (fun _=>1) v+profileCovariance μ k v:=by
    have hh:=profileCovariance_add_floor μ ell k v (by simpa only[one_smul] using hiG) hiK
    have hh':(fun x=>ell+k x)=c:=by funext x;dsimp[k];ring
    rwa[hh'] at hh
  have hR: (ell•profileCovariance μ (fun _=>1) v).PosSemidef:=hG.smul hell.le
  have hRange: (Matrix.toEuclideanCLM (𝕜:=ℝ) (ell•profileCovariance μ (fun _=>1) v)).range=
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariance μ (fun _=>1) v)).range:=
    covariance_range_smul _ hell.ne'
  filter_upwards[ae_frame_mem_gram_range μ v hv henergy] with x hx
  rw[he]
  apply PositiveMatrixRanges.range_le_add_right hR hK
  rwa[hRange]

/-- Actual bounded-Borel covariance differentiation of the complete word
along a uniformly elliptic continuum profile, including both baselines. -/
theorem hasDerivAt_profile_word
    (μ:Measure X){ell:ℝ}(hell:0<ell)(c:ℝ→X→ℝ)(e:X→ℝ)(v:X→State n){θ₀:ℝ}
    (hv:Measurable v)(henergy:Integrable (fun x=>‖v x‖^2) μ)
    (hc:∀θ,AEStronglyMeasurable (c θ) μ)(hci:∀θ,Integrable (fun x=>|c θ x| *‖v x‖^2) μ)
    (hclower:∀θ,∀ᵐx ∂μ,ell≤c θ x)(he:Measurable e)(g:X→ℝ)
    (hg0:∀ᵐx ∂μ,0≤g x)(hgi:Integrable (fun x=>g x*‖v x‖^2) μ)
    (hlip:∀ᵐx ∂μ,LipschitzWith (Real.nnabs (g x)) (fun θ=>c θ x))
    (hdiff:∀ᵐx ∂μ,HasDerivAt (fun θ=>c θ x) (e x) θ₀)
    (b a:State n→ℝ)(hb:Measurable b)(ha:Measurable a)(B M:ℝ)
    (hB:∀y,|b y|≤B)(hM:∀y,|a y|≤M)(z:State n):
    HasDerivAt (fun θ=>word (profileCovariance μ (c θ) v) b a z)
      ((1/2:ℝ)*∫x,e x*(∫y,centeredTest (profileCovariance μ (c θ₀) v) b a z y*
        MeasurableGaussianScores.secondScore (profileCovariance μ (c θ₀) v) (v x) y
        ∂multivariateGaussian 0 (profileCovariance μ (c θ₀) v)) ∂μ) θ₀:=by
  let A:=profileCovariance μ (c θ₀) v
  have hiA:=profileCovariance_integrable μ (c θ₀) v (hc θ₀) hv.aestronglyMeasurable (hci θ₀)
  have hA:A.PosSemidef:=profileCovariance_positive μ (c θ₀) v hiA
    ((hclower θ₀).mono (fun _ hx=>hell.le.trans hx))
  have hrange:=ae_frame_mem_profile_range μ v hv.aestronglyMeasurable henergy
    (c θ₀) (hc θ₀) (hci θ₀) hell (hclower θ₀)
  have hE:Integrable (fun x=>|e x| *‖v x‖^2) μ:=by
    apply hgi.mono' ((continuous_abs.measurable.comp he).mul (hv.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards[hlip,hdiff,hg0] with x hx hd hg
    rw[Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    have hb:=hd.le_of_lipschitz hx
    rw[Real.norm_eq_abs,Real.coe_nnabs,abs_of_nonneg hg] at hb
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hp:=hasDerivAt_profile_borel_of_uniform_floor μ hell c e v hv.aestronglyMeasurable henergy
    hc hci hclower he.aestronglyMeasurable g hg0 hgi hlip hdiff (fun y=>b y*a y) (hb.mul ha) (B*M)
    (fun y=>by rw[abs_mul];exact mul_le_mul (hB _) (hM _) (abs_nonneg _) ((abs_nonneg (b 0)).trans (hB 0))) z
  have hbr:=hasDerivAt_profile_borel_of_uniform_floor μ hell c e v hv.aestronglyMeasurable henergy
    hc hci hclower he.aestronglyMeasurable g hg0 hgi hlip hdiff b hb B hB z
  have har:=hasDerivAt_profile_borel_of_uniform_floor μ hell c e v hv.aestronglyMeasurable henergy
    hc hci hclower he.aestronglyMeasurable g hg0 hgi hlip hdiff a ha M hM z
  have hh:=hp.sub (hbr.mul har)
  convert! hh using 1
  rw[outer_centered_identity μ hA v hv hrange e he hE b a hb ha B M hB hM z]
  dsimp only[rawMark,GaussianCovarianceWord.average,gaussianAverage,A]
  ring

end SHE.GaussianWordCovarianceIntegral
