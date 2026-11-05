module

public import SHE.PastMeanDampedTime
public import SHE.MeanFreshBudget

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real PredictableL2
open scoped ENNReal NNReal
local instance pastMeanBudgetClock_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

def currentBudget (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν : ℝ) (q : ℝ≥0) : ℝ :=
  (Ioc base T).indicator (fun q=>(T-q)^(ρ/2)*
    QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν) q

theorem currentBudget_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν : ℝ) : Measurable (currentBudget P ell Cs k ρ base T fresh A0 ν) :=
  (((measurable_const.sub measurable_id).pow_const _).mul
    ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k (T-base) fresh A0 ν).comp
      (measurable_id.sub_const base)) |>.indicator measurableSet_Ioc).comp measurable_subtype_coe

/-- The original current-time clock sees the actual local window
(base,T]. The exact finite assignment budget is square-integrable iff
its proved fresh-degree margin is positive; no absolute-age bound is used. -/
theorem currentBudget_memLp (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ base T fresh A0 ν : ℝ) (hdegree : 0<ρ+2*fresh-1) (hT : base<T)
    (hν : 0≤ν) (H : ℝ≥0) :
    MemLp (currentBudget P ell Cs k ρ base T fresh A0 ν) 2 (timeMeasure H) := by
  have hm : Measurable (fun q : ℝ=>(T-q)^(ρ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν) :=
    ((measurable_const.sub measurable_id).pow_const _).mul
      ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k (T-base) fresh A0 ν).comp
        (measurable_id.sub_const base))
  have hw:=MeanRMSTimeFactors.fresh_budget_memLp P ell Cs k ρ (T-base) fresh A0 ν
    hdegree (sub_pos.mpr hT) hν
  have hwm : Measurable (fun w : ℝ=>w^(ρ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) ((T-base)-w) fresh A0 ν) :=
    (measurable_id.pow_const _).mul
      ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k (T-base) fresh A0 ν).comp
        (measurable_const.sub measurable_id))
  have hi : IntervalIntegrable (fun w : ℝ=>‖w^(ρ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) ((T-base)-w) fresh A0 ν‖^2)
      volume 0 (T-base):=(intervalIntegrable_iff_integrableOn_Ioc_of_le (sub_nonneg.mpr hT.le)).mpr
        ((memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mp hw)
  have hj : IntervalIntegrable (fun q : ℝ=>‖(T-q)^(ρ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν‖^2)
      volume base T := by
    simpa only [sub_zero,show T-(T-base)=base by ring,
      show ∀ q : ℝ,(T-base)-(T-q)=q-base by intro q;ring] using (hi.comp_sub_left T).symm
  have hs : MemLp (fun q : ℝ=>(T-q)^(ρ/2)*
      QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-base) (q-base) fresh A0 ν) 2
      (volume.restrict (Ioc base T)) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hj)
  have hind:=(memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hs
  have hr:=hind.mono_measure (Measure.restrict_le_self (μ:=volume) (s:=Ioc 0 (H:ℝ)))
  have hc : MeasurePreserving ((↑) : ℝ≥0→ℝ) (timeMeasure H) (volume.restrict (Ioc 0 (H:ℝ))) :=
    ⟨measurable_subtype_coe,timeMeasure_map H⟩
  exact hr.comp_measurePreserving hc

end SHE.PastMeanTimeFactors
