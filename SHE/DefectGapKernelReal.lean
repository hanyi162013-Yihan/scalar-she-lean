module
public import SHE.DefectGapMixtureIntegral
public import SHE.DefectOriginalConvolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
namespace SHE.DefectGapKernelReal
open Set MeasureTheory Real
open scoped NNReal ENNReal BigOperators

theorem measurable (Λ ρ:ℝ)(k:ℕ):Measurable
    (fun p:(Fin k→ℝ)×ℝ=>DefectGapKernelMass.realKernel Λ ρ k p.1 p.2):=by
  have ho:Measurable (DefectGapKernelMass.offsets k):=
    (DefectGapOffsets.offsets_measurable k).comp
      (Measurable.of_eval (fun i=>measurable_const.max (measurable_pi_apply i)))
  have hi(i:Fin (1+k)):Measurable (fun p:(Fin k→ℝ)×ℝ=>DefectGapKernelMass.offsets k p.1 i):=
    ((measurable_pi_apply i).comp ho).comp measurable_fst
  unfold DefectGapKernelMass.realKernel
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  unfold DefectCombinedTime.kernel SHE.newTimeKernel
  fun_prop

/-- Real-valued all-original-pair kernel L1, with its uniform exact
logarithmic mass. This is applicability, before multiplication by a
genuine random negative input. -/
theorem slice {Λ ρ h:ℝ}(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(hh:0≤h)(k:ℕ)(d:Fin k→ℝ):
    IntervalIntegrable (DefectGapKernelMass.realKernel Λ ρ k d) volume 0 h ∧
      (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k d τ ∂volume.restrict (Ioc (0:ℝ) h))≤
        DefectGapKernelMass.cost Λ ρ h k:=by
  have hmap:Measurable (fun τ:ℝ=>(d,τ)):=measurable_const.prodMk measurable_id
  have hm:=(measurable Λ ρ k).comp hmap
  have hn:∀ᵐτ:ℝ∂volume.restrict (Ioc (0:ℝ) h),0≤DefectGapKernelMass.realKernel Λ ρ k d τ:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact DefectGapMixtureIntegral.realKernel_nonneg hΛ.le k d hτ.1.le
  have hmass:=DefectGapKernelMass.mass hΛ hρ hρ1 hh k d
  have hi:IntegrableOn (DefectGapKernelMass.realKernel Λ ρ k d) (Ioc (0:ℝ) h) volume:=
    ⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hn).mpr
      (hmass.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mpr hi,?_⟩
  have he:=ofReal_integral_eq_lintegral_ofReal hi hn
  change ENNReal.ofReal (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k d τ
    ∂volume.restrict (Ioc (0:ℝ) h))=_ at he
  change (∫⁻τ:ℝ,ENNReal.ofReal (DefectGapKernelMass.realKernel Λ ρ k d τ)
    ∂volume.restrict (Ioc (0:ℝ) h))≤_ at hmass
  rw [←he] at hmass
  have hc:0≤DefectGapKernelMass.cost Λ ρ h k:=by
    have hl:0≤log (2+Λ*h):=log_nonneg (by nlinarith only [mul_nonneg hΛ.le hh])
    unfold DefectGapKernelMass.cost
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp hmass

/-- The same true kernel L1 and mass hold on the ORIGINAL current
clock after q↦terminal−q. No inverse-gap square majorant is used. -/
theorem current {Λ ρ a s h:ℝ}(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)
    (has:a≤s)(hspan:s-a≤h)(k:ℕ)(d:Fin k→ℝ):
    IntegrableOn (fun q:ℝ=>DefectGapKernelMass.realKernel Λ ρ k d (s-q)) (Ioc a s) volume ∧
      (∫q:ℝ,DefectGapKernelMass.realKernel Λ ρ k d (s-q) ∂volume.restrict (Ioc a s))≤
        DefectGapKernelMass.cost Λ ρ h k:=by
  have hh:=slice hΛ hρ hρ1 (sub_nonneg.mpr has) k d
  have hi:IntervalIntegrable (fun q:ℝ=>DefectGapKernelMass.realKernel Λ ρ k d (s-q)) volume a s:=by
    simpa only [sub_zero,sub_sub_cancel] using (hh.1.comp_sub_left s).symm
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le has).mp hi,?_⟩
  have he:=DefectOriginalConvolution.reflect_integral a s has
    (DefectGapKernelMass.realKernel Λ ρ k d) (fun _=>1)
  simp only [mul_one] at he
  rw [he]
  apply hh.2.trans
  unfold DefectGapKernelMass.cost
  have hlog:log (2+Λ*(s-a))≤log (2+Λ*h):=
    log_le_log (by nlinarith only [mul_nonneg hΛ.le (sub_nonneg.mpr has)])
      (by nlinarith only [mul_le_mul_of_nonneg_left hspan hΛ.le])
  exact mul_le_mul_of_nonneg_left (by linarith only [hlog]) (sq_nonneg _)
end SHE.DefectGapKernelReal
