module

public import SHE.PastCovarianceCurrentBudget
public import SHE.PastBaselineNativeBudget

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.MovingProfileBudget
open Set MeasureTheory
open scoped ENNReal
local instance movingProfileBudget_exponentFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩

def covariance (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν s : ℝ) : ℝ :=
  QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h s (MarkedProfileTimeFactors.freshDegree P) A0 ν

def baseline (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν s : ℝ) : ℝ :=
  if k=0 then 0 else BaselineOriginalGain.unitCoefficient P*
    QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h s (3/4:ℝ) A0 ν

def covarianceMass (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) : ℝ := ∫ s in Ioc (0:ℝ) h,(covariance P ell Cs k h A0 ν s)^2

def baselineMass (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) : ℝ := ∫ s in Ioc (0:ℝ) h,(baseline P ell Cs k h A0 ν s)^2

theorem covariance_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) : Measurable (covariance P ell Cs k h A0 ν) :=
  QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k h _ A0 ν

theorem baseline_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) : Measurable (baseline P ell Cs k h A0 ν) := by
  classical
  change Measurable (fun s=>if k=0 then (0:ℝ) else BaselineOriginalGain.unitCoefficient P*
    QuarterRMSTimeFactors.oldTimeBudget P ell Cs k h s (3/4:ℝ) A0 ν)
  by_cases hk:k=0
  · simp only [baseline,if_pos hk]
    exact measurable_const
  · simp only [baseline,if_neg hk]
    exact (QuarterRMSTimeFactors.oldTimeBudget_measurable P ell Cs k h _ A0 ν).const_mul _

theorem covariance_square_integrable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) (hh : 0<h) (hν : 0<ν) :
    Integrable (fun s=>(covariance P ell Cs k h A0 ν s)^2) (volume.restrict (Ioc 0 h)) :=
  MarkedProfileTimeFactors.all_depth_profile_budget_memLp P ell Cs k h A0 ν hh hν |>.integrable_sq

theorem baseline_square_integrable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) (hh : 0<h) (hν : 0<ν) :
    Integrable (fun s=>(baseline P ell Cs k h A0 ν s)^2) (volume.restrict (Ioc 0 h)) := by
  by_cases hk:k=0
  · simpa only [baseline,if_pos hk,zero_pow (by decide : (2:ℕ)≠0)] using
      (integrable_const (0:ℝ) : Integrable (fun _ : ℝ=>(0:ℝ)) (volume.restrict (Ioc 0 h)))
  · have hm:=PastBaselineTime.current_memLp P ell Cs k (by omega) 0 h A0 ν hh hν
    simpa only [baseline,if_neg hk,PastBaselineTime.budget,sub_zero] using hm.integrable_sq

theorem covarianceMass_nonneg (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) : 0≤covarianceMass P ell Cs k h A0 ν := integral_nonneg (fun _=>sq_nonneg _)
theorem baselineMass_nonneg (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (h A0 ν : ℝ) : 0≤baselineMass P ell Cs k h A0 ν := integral_nonneg (fun _=>sq_nonneg _)

end SHE.MovingProfileBudget
