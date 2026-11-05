module

public import SHE.MarkedProfileTimeFactors
public import SHE.QuarterBudgetClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.MarkedProfileTimeFactors
open Set Filter MeasureTheory Real StoppedFourier ProfileL2 QuarterRMSTimeFactors
open scoped ENNReal
local instance profileInputCurrentTime_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩

theorem freshDegree_gt_half (P : CanonicalCovariance.ProfileParameters) :
    (1/2:ℝ)<freshDegree P := by unfold freshDegree;linarith [P.exponent_pos]

/-- The signed-profile covariance-input budget is square integrable in
current time. The proof keeps the actual assignment budget and its root
masses; the sharper fresh degree is compared to the already checked
half-degree corner only for this integrability assertion. -/
theorem profileBudget_current_memLp (P : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (hk : 0<k) (T A0 ν : ℝ) (hT : 0<T) (hν : 0<ν) :
    MemLp (fun q=>oldTimeBudget P ell C k T q (freshDegree P) A0 ν) 2
      (volume.restrict (Ioc 0 T)) := by
  let f := freshDegree P
  let p := f-1/2
  have hf : 0<f := freshDegree_pos P
  have hp : 0≤p := (sub_pos.mpr (freshDegree_gt_half P)).le
  have hm := oldTimeBudget_measurable P ell C k T f A0 ν
  have hhalf := halfBudget_current_memLp P ell C k hk T A0 ν hT hν
  let K := T^p/(2*f)
  have hK : 0≤K := div_nonneg (rpow_nonneg hT.le _) (by positivity)
  have hdom := hhalf.norm.const_mul K
  apply hdom.mono' hm.aestronglyMeasurable
  have hqevent : ∀ᵐ q : ℝ ∂volume.restrict (Ioc 0 T),q∈Ioo 0 T := by
    rw [←Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0:ℝ) T=ᵐ[volume] Ioc 0 T)]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hqevent] with q hq
  have hw : 0<T-q := sub_pos.mpr hq.2
  have he : oldTimeBudget P ell C k T q f A0 ν=
      ((T-q)^p/(2*f))*oldTimeBudget P ell C k T q (1/2:ℝ) A0 ν := by
    have hs := oldTimeBudget_scaling P ell C k T q (1/2:ℝ) f A0 ν hq.2 (by norm_num) hf
    dsimp only [p]
    convert! congrArg (fun z : ℝ=>z/(2*f)) hs.symm using 1 <;>
      field_simp [hf.ne'] <;> ring
  have hcoef : (T-q)^p/(2*f)≤K :=
    div_le_div_of_nonneg_right (rpow_le_rpow hw.le (by linarith [hq.1]) hp) (by positivity)
  change |oldTimeBudget P ell C k T q f A0 ν|≤K*|oldTimeBudget P ell C k T q (1/2:ℝ) A0 ν|
  rw [he,abs_mul,abs_of_nonneg (div_nonneg (rpow_nonneg hw.le _) (by positivity))]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

end SHE.MarkedProfileTimeFactors
