module

public import SHE.PastMeanBudgetMass
public import SHE.MovingPastFractional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.MovingMeanKernelMass
open Set MeasureTheory Real PredictableL2
open scoped ENNReal

/-- The exact relative current kernel left by the old-time mean RMS
estimate, before averaging the actual current input energy. -/
def kernel (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν : ℝ) (s : ℝ) : ℝ :=
  ((h-s)^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h s fresh A0 ν)^2

theorem kernel_nonneg (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν s : ℝ) : 0≤kernel P ell Cs k ρ h fresh A0 ν s := sq_nonneg _

theorem kernel_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν : ℝ) : Measurable (kernel P ell Cs k ρ h fresh A0 ν) :=
  (((measurable_const.sub measurable_id).pow_const _).mul
    (QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k h fresh A0 ν)).pow_const 2

/-- Reflection of the true relative current age gives genuine L1
kernel mass; its sharp finite assignment budget is retained. -/
theorem kernel_mass (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν : ℝ) (hd : 0<ρ+2*fresh-1) (hh : 0<h) (hν : 0≤ν) :
    Integrable (kernel P ell Cs k ρ h fresh A0 ν) (volume.restrict (Ioc (0:ℝ) h)) ∧
      (∫ s,kernel P ell Cs k ρ h fresh A0 ν s ∂volume.restrict (Ioc (0:ℝ) h))≤
        PastMeanTimeFactors.assignmentMass P ell Cs k ρ h fresh A0 ν := by
  let g : ℝ→ℝ:=fun w=>(w^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h (h-w) fresh A0 ν)^2
  have hgm : Measurable (fun w : ℝ=>w^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h (h-w) fresh A0 ν):=
    (measurable_id.pow_const _).mul
      ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k h fresh A0 ν).comp (measurable_const.sub measurable_id))
  have hgi : Integrable g (volume.restrict (Ioc (0:ℝ) h)):=by
    simpa only [g,Real.norm_eq_abs,sq_abs] using
      (memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).mp
        (MeanRMSTimeFactors.fresh_budget_memLp P ell Cs k ρ h fresh A0 ν hd hh hν)
  have hinterval : IntervalIntegrable g volume 0 h:=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).mpr hgi
  have hi : Integrable (kernel P ell Cs k ρ h fresh A0 ν) (volume.restrict (Ioc (0:ℝ) h)):=by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).mp
    change IntervalIntegrable (fun s : ℝ=>((h-s)^(ρ/2)*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h s fresh A0 ν)^2) volume 0 h
    simpa only [g,kernel,sub_zero,sub_self,sub_sub_cancel] using (hinterval.comp_sub_left h).symm
  refine ⟨hi,?_⟩
  have he : (∫ s,kernel P ell Cs k ρ h fresh A0 ν s ∂volume.restrict (Ioc (0:ℝ) h))=
      ∫ w,g w ∂volume.restrict (Ioc (0:ℝ) h):=by
    rw [←intervalIntegral.integral_of_le hh.le,←intervalIntegral.integral_of_le hh.le]
    simpa only [g,kernel,sub_zero,sub_self,sub_sub_cancel] using
      intervalIntegral.integral_comp_sub_left g h (a:=0) (b:=h)
  rw [he]
  exact MeanRMSTimeFactors.fresh_budget_square_bound P ell Cs k ρ h fresh A0 ν hd hh hν

theorem kernel_lintegral (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν : ℝ) (hd : 0<ρ+2*fresh-1) (hh : 0<h) (hν : 0≤ν) :
    (∫⁻ s in Ioc (0:ℝ) h,ENNReal.ofReal (kernel P ell Cs k ρ h fresh A0 ν s))≤
      ENNReal.ofReal (PastMeanTimeFactors.assignmentMass P ell Cs k ρ h fresh A0 ν) := by
  have hi:=kernel_mass P ell Cs k ρ h fresh A0 ν hd hh hν
  rw [←ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (kernel_nonneg P ell Cs k ρ h fresh A0 ν))]
  exact ENNReal.ofReal_le_ofReal hi.2

end SHE.MovingMeanKernelMass
