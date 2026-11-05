module

public import SHE.ProfileInputCurrentTime
public import SHE.QuarterRMSOldTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.MarkedProfileTimeFactors
open Set MeasureTheory Real QuarterRMSTimeFactors PhysicalAssignmentGapScale GaussianAssignmentBlocks
  AllocatedAssignmentKernel CoveredHistoryGeometry AssignmentGapPartition
open scoped BigOperators ENNReal NNReal

/-- At leading depth the covariance-profile budget is its genuine
integrable power kernel. The half-degree comparison is unnecessary. -/
theorem leading_budget_eq (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (T q fresh A0 ν : ℝ) :
    oldTimeBudget P ell Cs 0 T q fresh A0 ν=(A0/fresh)*(T-q)^(fresh-1) := by
  simp [oldTimeBudget,assignments,scorePrefactor,prefactor,
    roughCount,rootCount,emptyCount,inverseDegreeProduct,block]
  ring

theorem leading_profile_budget_memLp (P : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (Cs : ℕ→ℝ) (T A0 ν : ℝ) (hT : 0<T) :
    MemLp (fun q=>oldTimeBudget P ell Cs 0 T q (freshDegree P) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  let a := freshDegree P-1
  have ha : -1<a*2 := by
    dsimp only [a]
    linarith [freshDegree_gt_half P]
  have hp : IntervalIntegrable (fun w : ℝ=>w^(a*2)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' ha
  have hq : IntervalIntegrable (fun q : ℝ=>(T-q)^(a*2)) volume 0 T := by
    simpa only [sub_zero,sub_self] using (hp.comp_sub_left T).symm
  have hi : Integrable (fun q : ℝ=>(T-q)^(a*2)) (volume.restrict (Ioc 0 T)) := by
    change IntegrableOn (fun q : ℝ=>(T-q)^(a*2)) (Ioc 0 T) volume
    simpa only [uIoc_of_le hT.le] using hq.1
  have hm := oldTimeBudget_measurable P ell Cs 0 T (freshDegree P) A0 ν
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (hi.const_mul ((A0/freshDegree P)^2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hmem
  rw [leading_budget_eq,Real.norm_eq_abs,abs_mul,mul_pow,sq_abs,sq_abs,
    ←Real.rpow_mul_natCast (sub_nonneg.mpr hmem.2)]
  rfl

theorem all_depth_profile_budget_memLp (P : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) :
    MemLp (fun q=>oldTimeBudget P ell Cs k T q (freshDegree P) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  cases k with
  | zero => exact leading_profile_budget_memLp P ell Cs T A0 ν hT
  | succ k => exact profileBudget_current_memLp P ell Cs (k+1) (by omega) T A0 ν hT hν

def profileCurrentBudget (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (T A0 ν : ℝ) (q : ℝ≥0) : ℝ :=
  (Ioc (0:ℝ) T).indicator (fun q=>oldTimeBudget P ell Cs k T q (freshDegree P) A0 ν) q

/-- Full covariance-profile current budget at EVERY finite order,
including zero, on the original nonnegative current-time measure. -/
theorem profile_current_memLp (P : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) (H : ℝ≥0) :
    MemLp (profileCurrentBudget P ell Cs k T A0 ν) 2 (PredictableL2.timeMeasure H) := by
  have hi := (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr
    (all_depth_profile_budget_memLp P ell Cs k T A0 ν hT hν)
  have hr := hi.mono_measure (Measure.restrict_le_self (μ:=volume) (s:=Ioc 0 (H:ℝ)))
  have hc : MeasurePreserving ((↑) : ℝ≥0→ℝ) (PredictableL2.timeMeasure H)
      (volume.restrict (Ioc 0 (H:ℝ))) :=
    ⟨measurable_subtype_coe,PredictableL2.timeMeasure_map H⟩
  exact hr.comp_measurePreserving hc

end SHE.MarkedProfileTimeFactors
