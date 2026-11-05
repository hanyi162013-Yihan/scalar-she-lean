module

public import SHE.BaselineTimeLedger

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.BaselineTimeLedger
open Set Filter MeasureTheory Real StoppedFourier ProfileL2 QuarterRMSTimeFactors
open scoped ENNReal
local instance baselineCurrentTime_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

/-- The actual baseline old-time budget is square integrable in current
time, retaining its fresh degree3/4 and all original assignment masses. -/
theorem baselineBudget_current_memLp (P : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (hk : 0<k) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) :
    MemLp (fun q=>oldTimeBudget P ell C k T q (3/4:ℝ) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  have hm := oldTimeBudget_measurable P ell C k T (3/4:ℝ) A0 ν
  have hhalf := halfBudget_current_memLp P ell C k hk T A0 ν hT hν
  let K := T^(1/4:ℝ)/(3/2:ℝ)
  have hK : 0≤K := by unfold K;positivity
  apply (hhalf.norm.const_mul K).mono' hm.aestronglyMeasurable
  have hqevent : ∀ᵐ q : ℝ ∂volume.restrict (Ioc 0 T),q∈Ioo 0 T := by
    rw [←Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0:ℝ) T=ᵐ[volume] Ioc 0 T)]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hqevent] with q hq
  have hw : 0<T-q := sub_pos.mpr hq.2
  have he : oldTimeBudget P ell C k T q (3/4:ℝ) A0 ν=
      ((T-q)^(1/4:ℝ)/(3/2:ℝ))*oldTimeBudget P ell C k T q (1/2:ℝ) A0 ν := by
    have hs := oldTimeBudget_scaling P ell C k T q (1/2:ℝ) (3/4:ℝ) A0 ν hq.2 (by norm_num) (by norm_num)
    convert! congrArg (fun z : ℝ=>z/(3/2:ℝ)) hs.symm using 1 <;> norm_num <;> ring
  have hcoef : (T-q)^(1/4:ℝ)/(3/2:ℝ)≤K :=
    div_le_div_of_nonneg_right (rpow_le_rpow hw.le (by linarith [hq.1]) (by norm_num)) (by norm_num)
  change |oldTimeBudget P ell C k T q (3/4:ℝ) A0 ν|≤K*|oldTimeBudget P ell C k T q (1/2:ℝ) A0 ν|
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(T-q)^(1/4:ℝ)/(3/2:ℝ))]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- Depth zero has no baseline derivative term, so the complete scaled
baseline budget is L2 at EVERY finite depth, without a separate leading
baseline estimate. -/
theorem scaled_current_memLp (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) :
    MemLp (fun q=>inputConstant P d k*oldTimeBudget P ell C k T q (3/4:ℝ) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  by_cases hk : 0<k
  · exact (baselineBudget_current_memLp P ell C k hk T A0 ν hT hν).const_mul _
  · have hk0 : k=0 := by omega
    subst k
    have hz : inputConstant P d 0=0 := by
      simp only [inputConstant,BaselineAssignmentScale.Index,Fintype.card_prod,Fintype.card_fin,
        Nat.cast_mul,Nat.cast_zero,zero_mul]
    simp only [hz,zero_mul]
    exact MemLp.zero

end SHE.BaselineTimeLedger
