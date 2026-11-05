module

public import SHE.ProfileLeadingBudget
public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastCovarianceCurrentBudget
open Set MeasureTheory Real PredictableL2 QuarterRMSTimeFactors MarkedProfileTimeFactors
open scoped ENNReal NNReal
local instance : Fact ((2:ℝ≥0∞)≠⊤):=⟨by simp⟩

def budget (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν q : ℝ) : ℝ:=
  oldTimeBudget P ell Cs k (T-v) (q-v) (freshDegree P) A0 ν

theorem budget_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) : Measurable (budget P ell Cs k v T A0 ν):=
  (oldTimeBudget_measurable P ell Cs k (T-v) (freshDegree P) A0 ν).comp (measurable_id.sub_const v)

/-- The true relative covariance budget is L2 in original current time,
at every finite depth including zero. -/
theorem current_memLp (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) (hvT : v<T) (hν : 0<ν) :
    MemLp (budget P ell Cs k v T A0 ν) 2 (volume.restrict (Ioc v T)) := by
  have hm:=all_depth_profile_budget_memLp P ell Cs k (T-v) A0 ν (sub_pos.mpr hvT) hν
  have hs : MeasurePreserving (fun q : ℝ=>q-v) (volume.restrict (Ioc v T))
      (volume.restrict (Ioc (0:ℝ) (T-v))) := by
    have ha:=(measurePreserving_add_right (volume:Measure ℝ) (-v)).restrict_preimage
      (s:=Ioc (0:ℝ) (T-v)) measurableSet_Ioc
    have he : (fun q : ℝ=>q+(-v))⁻¹' Ioc (0:ℝ) (T-v)=Ioc v T:=by
      ext q
      simp only [mem_preimage,mem_Ioc]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    rw [he] at ha
    simpa only [sub_eq_add_neg] using ha
  exact hm.comp_measurePreserving hs

def currentBudget (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) (q : ℝ≥0) : ℝ:=
  (Ioc v T).indicator (budget P ell Cs k v T A0 ν) q

theorem currentBudget_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) : Measurable (currentBudget P ell Cs k v T A0 ν):=
  ((budget_measurable P ell Cs k v T A0 ν).indicator measurableSet_Ioc).comp measurable_subtype_coe

theorem native_current_memLp (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν : ℝ) (hvT : v<T) (hν : 0<ν) (H : ℝ≥0) :
    MemLp (currentBudget P ell Cs k v T A0 ν) 2 (timeMeasure H) := by
  have hi:=(memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr
    (current_memLp P ell Cs k v T A0 ν hvT hν)
  have hr:=hi.mono_measure (Measure.restrict_le_self (μ:=volume) (s:=Ioc 0 (H:ℝ)))
  have hc : MeasurePreserving ((↑) : ℝ≥0→ℝ) (timeMeasure H) (volume.restrict (Ioc 0 (H:ℝ))):=
    ⟨measurable_subtype_coe,timeMeasure_map H⟩
  exact hr.comp_measurePreserving hc

end SHE.PastCovarianceCurrentBudget
