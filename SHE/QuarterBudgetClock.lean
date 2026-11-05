module

public import SHE.QuarterBudgetSquare
public import SHE.PredictableL2

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace SHE.QuarterRMSTimeFactors
open Set MeasureTheory Real PhysicalAssignmentGapScale GaussianAssignmentBlocks
  AllocatedAssignmentKernel CoveredHistoryGeometry PredictableL2
open scoped ENNReal NNReal BigOperators
local instance quarterBudgetClock_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

theorem oldTimeBudget_measurable (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (T fresh A0 ν : ℝ) :
    Measurable (fun q => oldTimeBudget Q ell Cs k T q fresh A0 ν) := by
  unfold oldTimeBudget
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul
    ((measurable_const.mul ((measurable_const.sub measurable_id).pow_const _)).mul
      (((rootMass_measurable _).comp (measurable_const.sub measurable_id)).pow_const _))

/-- The true current-time budget, with q=T-w, is L2. Reflection of the
actual finite Lebesgue interval is justified before changing the clock. -/
theorem halfBudget_current_memLp (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (hk : 0<k) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) :
    MemLp (fun q => oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  have hm : Measurable (fun q => oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν) :=
    oldTimeBudget_measurable Q ell Cs k T (1/2:ℝ) A0 ν
  have hw := halfBudget_memLp Q ell Cs k hk T A0 ν hT hν
  have hwm : Measurable (fun w => oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν) :=
    hm.comp (measurable_const.sub measurable_id)
  have hi : IntervalIntegrable (fun w => ‖oldTimeBudget Q ell Cs k T (T-w) (1/2:ℝ) A0 ν‖^2)
      volume 0 T := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
        ((memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mp hw)
  have hj : IntervalIntegrable (fun q => ‖oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν‖^2)
      volume 0 T := by
    simpa only [sub_zero,sub_self,show ∀ q : ℝ,T-(T-q)=q by intro q;ring] using
      (hi.comp_sub_left T).symm
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hj.1

def currentBudget (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (T A0 ν : ℝ) (q : ℝ≥0) : ℝ :=
  (Ioc (0:ℝ) T).indicator (fun q => oldTimeBudget Q ell Cs k T q (1/2:ℝ) A0 ν) q

/-- The current-time budget is genuinely L2 for the ORIGINAL NNReal
Itô time measure, with no implicit replacement by a real-time measure. -/
theorem currentBudget_memLp (Q : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (hk : 0<k) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) (H : ℝ≥0) :
    MemLp (currentBudget Q ell Cs k T A0 ν) 2 (timeMeasure H) := by
  have hi := (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr
    (halfBudget_current_memLp Q ell Cs k hk T A0 ν hT hν)
  have hr := hi.mono_measure (Measure.restrict_le_self (μ:=volume) (s:=Ioc 0 (H:ℝ)))
  have hc : MeasurePreserving ((↑) : ℝ≥0→ℝ) (timeMeasure H) (volume.restrict (Ioc 0 (H:ℝ))) :=
    ⟨measurable_subtype_coe,timeMeasure_map H⟩
  exact hr.comp_measurePreserving hc

end SHE.QuarterRMSTimeFactors
