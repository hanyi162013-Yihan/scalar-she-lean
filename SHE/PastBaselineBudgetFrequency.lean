module

public import SHE.PastBaselineNativeBudget
public import SHE.MeanAssignmentFrequency

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.PastBaselineNativeBudget
open Set MeasureTheory Real PredictableL2
open scoped NNReal ENNReal

/-- For every positive depth, the restored baseline clock is exactly
one fixed profile coefficient times the general rho=0, fresh=3/4 clock.
No frequency or current time occurs in that coefficient. -/
theorem currentBudget_eq_mean (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (hk : k≠0) (v T A0 ν : ℝ) (q : ℝ≥0) :
    currentBudget P ell Cs k v T A0 ν q=BaselineOriginalGain.unitCoefficient P*
      PastMeanTimeFactors.currentBudget P ell Cs k 0 v T (3/4:ℝ) A0 ν q := by
  classical
  by_cases hq : (q:ℝ)∈Ioc v T
  · simp only [currentBudget,ite_eq_right hk,PastBaselineTime.budget,
      PastMeanTimeFactors.currentBudget,indicator_of_mem hq,zero_div,rpow_zero,one_mul]
  · simp only [currentBudget,ite_eq_right hk,PastMeanTimeFactors.currentBudget,
      indicator_of_notMem hq,mul_zero]

/-- The baseline frequency constant is exactly zero at depth zero.
At positive depth it preserves all original assignment masses. -/
def frequencyConstant (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (span η : ℝ) : ℝ:=
  if k=0 then 0 else (BaselineOriginalGain.unitCoefficient P)^2*
    PastMeanTimeFactors.assignmentFrequencyConstant P ell Cs k 0 span (3/4:ℝ) 1 η

/-- Every fixed finite baseline depth admits arbitrarily small root
frequency loss on the ORIGINAL native clock, with exact root amplitude
and no loss in the past difference input. -/
theorem current_frequency_bound (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (v T A0 ν η : ℝ) (hvT : v<T) (hspan1 : T-v≤1)
    (hν : 0≤ν) (hη : 0<η) (H : ℝ≥0) :
    (∫ q,currentBudget P ell Cs k v T A0 ν q^2 ∂timeMeasure H)≤
      A0^2*frequencyConstant P ell Cs k (T-v) η*(1+ν)^η := by
  classical
  by_cases hk:k=0
  · simp only [currentBudget,frequencyConstant,ite_eq_left hk,zero_pow (by norm_num : (2:ℕ)≠0),
      integral_zero,mul_zero,zero_mul,le_refl]
  · have hm:=PastMeanTimeFactors.currentBudget_assignment_bound P ell Cs k 0 v T (3/4:ℝ)
      A0 ν (by norm_num) hvT hν H
    have hf:=PastMeanTimeFactors.assignmentMass_frequency_bound P ell Cs k 0 (T-v) (3/4:ℝ)
      A0 η (by norm_num) (sub_nonneg.mpr hvT.le) hspan1 hη hν
    rw [PastMeanTimeFactors.assignmentFrequencyConstant_amplitude] at hf
    have hh:=mul_le_mul_of_nonneg_left (hm.trans hf) (sq_nonneg (BaselineOriginalGain.unitCoefficient P))
    simp only [currentBudget_eq_mean P ell Cs k hk,mul_pow,integral_const_mul]
    convert! hh using 1 <;> simp only [frequencyConstant,ite_eq_right hk] <;> ring

end SHE.PastBaselineNativeBudget
