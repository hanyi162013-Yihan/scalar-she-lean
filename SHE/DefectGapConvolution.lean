module
public import SHE.DefectGapMixtureIntegral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.DefectGapConvolution
open Set MeasureTheory Real
open scoped NNReal ENNReal BigOperators

def truncated (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (Λ ρ u A0 ν:ℝ)(k:ℕ)(f:ℝ→ℝ)(T:ℝ):ℝ:=
  ∫d:Fin k→ℝ,if (∀i,0<d i) ∧ (∑i,d i)<u then
    DefectGapDensity.raw P ell C k A0 ν d*
      (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k d τ*f (T-(∑i,d i)-τ)
        ∂volume.restrict (Ioc (0:ℝ) (u-(∑i,d i))))
  else 0

/-- Enlarging the original positive gap/slack simplex to the COMPLETE
fixed history/kernel mixture preserves the actual translated input
inside the time integral. No pointwise stochastic energy cap is used
for this quantitative inequality; boundedness is only L1 applicability. -/
theorem le_mixture (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h A0 ν u:ℝ}
    (hell:0<ell)(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(hh:0<h)(hu:u≤h)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hν:0≤ν)
    (f:ℝ→ℝ)(hf:Measurable f)(hn:∀q,0≤f q)(B:ℝ)(hb:∀q,f q≤B)(T:ℝ):
    truncated P ell C Λ ρ u A0 ν k f T≤
      ∫p:(Fin k→ℝ)×ℝ,f (T-(∑i,p.1 i)-p.2)
        ∂DefectGapMixture.measure P ell C Λ ρ h A0 ν k:=by
  let D:=DefectGapDensity.density P ell C k h A0 ν
  let K:=DefectGapKernelMass.realKernel Λ ρ k
  let J:((Fin k→ℝ)×ℝ)→ℝ:=fun p=>f (T-(∑i,p.1 i)-p.2)
  let κ:=DefectGapMixture.measure P ell C Λ ρ h A0 ν k
  letI:IsFiniteMeasure κ:=DefectGapMixture.finite P hell hΛ hρ hρ1 hh C hC k hA0 hν
  have hJ:Measurable J:=hf.comp
    ((measurable_const.sub (Finset.measurable_sum _ (fun i _=>
      (measurable_pi_apply i).comp measurable_fst))).sub measurable_snd)
  have hiJ:Integrable J κ:=(integrable_const B).mono' hJ.aestronglyMeasurable (by
    filter_upwards with p
    rw [Real.norm_of_nonneg (hn _)]
    exact hb _)
  have hw:=DefectGapMixtureIntegral.integral P hell hΛ.le C hC k hA0 hν J hiJ
  let G:((Fin k→ℝ)×ℝ)→ℝ:=fun p=>D p.1*K p.1 p.2*J p
  have hiG:Integrable G ((volume:Measure (Fin k→ℝ)).prod (volume.restrict (Ioc (0:ℝ) h))):=hw.1
  let U:(Fin k→ℝ)→ℝ:=fun d=>D d*(∫τ:ℝ,K d τ*f (T-(∑i,d i)-τ)
    ∂volume.restrict (Ioc (0:ℝ) h))
  have heU(d:Fin k→ℝ):(∫τ:ℝ,G (d,τ) ∂volume.restrict (Ioc (0:ℝ) h))=U d:=by
    simpa only [G,J,U,mul_assoc] using
      integral_const_mul (D d) (fun τ=>K d τ*f (T-(∑i,d i)-τ))
  have hiU:Integrable U volume:=hiG.integral_prod_left.congr (ae_of_all _ heU)
  have hnU(d:Fin k→ℝ):0≤U d:=by
    apply mul_nonneg (DefectGapDensity.density_nonneg P hell C hC k hA0 hν d)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact mul_nonneg (DefectGapMixtureIntegral.realKernel_nonneg hΛ.le k d hτ.1.le) (hn _)
  have hnl(d:Fin k→ℝ):0≤(if (∀i,0<d i) ∧ (∑i,d i)<u then
      DefectGapDensity.raw P ell C k A0 ν d*
        (∫τ:ℝ,K d τ*f (T-(∑i,d i)-τ) ∂volume.restrict (Ioc (0:ℝ) (u-(∑i,d i)))) else 0):=by
    split_ifs with hd
    · apply mul_nonneg (DefectGapDensity.raw_nonneg P hell C hC k hA0 hν d hd.1)
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
      exact mul_nonneg (DefectGapMixtureIntegral.realKernel_nonneg hΛ.le k d hτ.1.le) (hn _)
    · exact le_refl 0
  have hmono:∀ᵐd:Fin k→ℝ∂volume,
      (if (∀i,0<d i) ∧ (∑i,d i)<u then DefectGapDensity.raw P ell C k A0 ν d*
        (∫τ:ℝ,K d τ*f (T-(∑i,d i)-τ) ∂volume.restrict (Ioc (0:ℝ) (u-(∑i,d i)))) else 0)≤U d:=by
    filter_upwards [hiG.prod_right_ae] with d hid
    by_cases hd:(∀i,0<d i) ∧ (∑i,d i)<u
    · have hdH:(∀i,0<d i) ∧ (∑i,d i)<h:=⟨hd.1,hd.2.trans_le hu⟩
      have heD:D d=DefectGapDensity.raw P ell C k A0 ν d:=by
        exact if_pos hdH
      have hs:0≤∑i,d i:=Finset.sum_nonneg (fun i _=>(hd.1 i).le)
      have hlen:u-(∑i,d i)≤h:=by linarith
      simp only [if_pos hd,U,heD]
      rw [←integral_const_mul,←integral_const_mul]
      apply setIntegral_mono_set
        (f:=fun τ=>DefectGapDensity.raw P ell C k A0 ν d*(K d τ*f (T-(∑i,d i)-τ)))
      · change Integrable (fun τ=>DefectGapDensity.raw P ell C k A0 ν d*
          (K d τ*f (T-(∑i,d i)-τ))) (volume.restrict (Ioc (0:ℝ) h))
        simpa only [G,J,heD,mul_assoc] using hid
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
        exact mul_nonneg (DefectGapDensity.raw_nonneg P hell C hC k hA0 hν d hd.1)
          (mul_nonneg (DefectGapMixtureIntegral.realKernel_nonneg hΛ.le k d hτ.1.le) (hn _))
      · exact ae_of_all _ (fun τ hτ=>⟨hτ.1,hτ.2.trans hlen⟩)
    · simp only [if_neg hd]
      exact hnU d
  unfold truncated
  calc
    _≤∫d:Fin k→ℝ,U d:=integral_mono_of_nonneg (ae_of_all _ hnl) hiU hmono
    _=_:=hw.2.symm
end SHE.DefectGapConvolution
