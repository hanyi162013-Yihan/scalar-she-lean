module

public import SHE.MovingProfileBudget
public import SHE.MovingMeanKernelMass
public import SHE.PastBaselineBudgetFrequency

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.MovingProfileBudget
open Set MeasureTheory Real

/-- On a fixed window, the actual moving covariance clock has an
arbitrarily small frequency loss and exact quadratic root amplitude. -/
theorem covarianceMass_frequency (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν η : ℝ) (hh : 0<h) (hh1 : h≤1) (hν : 0≤ν) (hη : 0<η) :
    covarianceMass P ell Cs k h A0 ν≤A0^2*
      PastMeanTimeFactors.assignmentFrequencyConstant P ell Cs k 0 h
        (MarkedProfileTimeFactors.freshDegree P) 1 η*(1+ν)^η := by
  have hd : 0<(0:ℝ)+2*MarkedProfileTimeFactors.freshDegree P-1 := by
    linarith [MarkedProfileTimeFactors.freshDegree_gt_half P]
  have hm:=MovingMeanKernelMass.kernel_mass P ell Cs k 0 h
    (MarkedProfileTimeFactors.freshDegree P) A0 ν hd hh hν
  have hf:=PastMeanTimeFactors.assignmentMass_frequency_bound P ell Cs k 0 h
    (MarkedProfileTimeFactors.freshDegree P) A0 η hd hh.le hh1 hη hν
  rw [PastMeanTimeFactors.assignmentFrequencyConstant_amplitude] at hf
  apply (show covarianceMass P ell Cs k h A0 ν≤
      PastMeanTimeFactors.assignmentMass P ell Cs k 0 h
        (MarkedProfileTimeFactors.freshDegree P) A0 ν from ?_).trans hf
  simpa only [covarianceMass,covariance,MovingMeanKernelMass.kernel,zero_div,rpow_zero,one_mul] using hm.2

/-- The moving baseline budget retains the exact zero-depth
cancellation and the same fixed-depth frequency loss. -/
theorem baselineMass_frequency (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν η : ℝ) (hh : 0<h) (hh1 : h≤1) (hν : 0≤ν) (hη : 0<η) :
    baselineMass P ell Cs k h A0 ν≤A0^2*
      PastBaselineNativeBudget.frequencyConstant P ell Cs k h η*(1+ν)^η := by
  classical
  by_cases hk:k=0
  · simp only [baselineMass,baseline,if_pos hk,zero_pow (by decide : (2:ℕ)≠0),integral_zero,
      PastBaselineNativeBudget.frequencyConstant,if_pos hk,mul_zero,zero_mul,le_refl]
  · have hm:=MovingMeanKernelMass.kernel_mass P ell Cs k 0 h (3/4:ℝ) A0 ν (by norm_num) hh hν
    have hf:=PastMeanTimeFactors.assignmentMass_frequency_bound P ell Cs k 0 h (3/4:ℝ)
      A0 η (by norm_num) hh.le hh1 hη hν
    rw [PastMeanTimeFactors.assignmentFrequencyConstant_amplitude] at hf
    have hb:=mul_le_mul_of_nonneg_left (hm.2.trans hf)
      (sq_nonneg (BaselineOriginalGain.unitCoefficient P))
    simpa only [baselineMass,baseline,if_neg hk,mul_pow,integral_const_mul,
      PastBaselineNativeBudget.frequencyConstant,if_neg hk,MovingMeanKernelMass.kernel,
      zero_div,rpow_zero,one_mul,mul_assoc,mul_left_comm ((BaselineOriginalGain.unitCoefficient P)^2)] using hb

end SHE.MovingProfileBudget
