module

public import SHE.PastBaselineTime
public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastBaselineNativeBudget
open Set MeasureTheory Real PredictableL2
open scoped ENNReal NNReal
local instance pastBaselineNativeBudget_finite : Fact ((2:ℝ≥0∞)≠⊤):=⟨by simp⟩

def currentBudget (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) (q : ℝ≥0) : ℝ:=
  if k=0 then 0 else (Ioc v T).indicator
    (fun r=>PastBaselineTime.budget P ell Cs k T v r A0 ν) q

theorem currentBudget_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) : Measurable (currentBudget P ell Cs k v T A0 ν):=by
  classical
  by_cases hk:k=0
  · have he : currentBudget P ell Cs k v T A0 ν = (fun _=>0) :=
      funext (fun q=>by simp only [currentBudget,ite_eq_left hk])
    rw [he]
    exact measurable_const
  · have hm : Measurable (fun r=>PastBaselineTime.budget P ell Cs k T v r A0 ν):=by
      unfold PastBaselineTime.budget
      exact ((QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k (T-v) (3/4:ℝ) A0 ν).comp
        (measurable_id.sub_const v)).const_mul _
    have he : currentBudget P ell Cs k v T A0 ν =
        (fun q:ℝ≥0=>(Ioc v T).indicator
          (fun r=>PastBaselineTime.budget P ell Cs k T v r A0 ν) (q:ℝ)) :=
      funext (fun q=>by simp only [currentBudget,ite_eq_right hk])
    rw [he]
    exact (hm.indicator (s:=Ioc v T) measurableSet_Ioc).comp measurable_subtype_coe

/-- Genuine current-time square integrability of the original relative
baseline budget on the native Ito clock. Depth zero is EXACTLY zero,
because there is no baseline leaf at that depth. -/
theorem native_current_memLp (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) (hvT : v<T) (hν : 0<ν) (H : ℝ≥0) :
    MemLp (currentBudget P ell Cs k v T A0 ν) 2 (timeMeasure H) := by
  by_cases hk:k=0
  · have he : currentBudget P ell Cs k v T A0 ν = (fun _=>0) :=
      funext (fun q=>by simp only [currentBudget,ite_eq_left hk])
    rw [he]
    exact MemLp.zero
  · have hm:=PastBaselineTime.current_memLp P ell Cs k (by omega) v T A0 ν hvT hν
    have hi:=(memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hm
    have hr:=hi.mono_measure (Measure.restrict_le_self (μ:=volume) (s:=Ioc 0 (H:ℝ)))
    have hc : MeasurePreserving ((↑) : ℝ≥0→ℝ) (timeMeasure H) (volume.restrict (Ioc 0 (H:ℝ))):=
      ⟨measurable_subtype_coe,timeMeasure_map H⟩
    have he : currentBudget P ell Cs k v T A0 ν =
        (fun q:ℝ≥0=>(Ioc v T).indicator
          (fun r=>PastBaselineTime.budget P ell Cs k T v r A0 ν) (q:ℝ)) :=
      funext (fun q=>by simp only [currentBudget,ite_eq_right hk])
    rw [he]
    exact hr.comp_measurePreserving hc

end SHE.PastBaselineNativeBudget
