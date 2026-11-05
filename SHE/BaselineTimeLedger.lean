module

public import SHE.OmittedTimeFields
public import SHE.ProfileInputOldTime
public import SHE.ProfileInputCurrentTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.BaselineTimeLedger
open Set MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays CoveredControlledLaw PhysicalParentGeometry PhysicalScoreChain
  PhysicalAssignmentGapScale QuarterRMSTimeFactors HistoryProductMeasure QuarterSpatialEvent
  ControlledScoreRates ProfileL2 BaselineAssignmentScale
open scoped BigOperators
open Classical
local instance baselineTimeLedger_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)

def inputConstant (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) (k : ℕ) : ℝ :=
  (Fintype.card (Index k):ℝ)*BaselineOriginalGain.unitSharp P d

theorem inputConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (d : CircleL2) (k : ℕ) :
    0 ≤ inputConstant P d k := mul_nonneg (Nat.cast_nonneg _) (BaselineOriginalGain.unitSharp_nonneg P d)

def gainDensity (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) : ℝ :=
  if StrictHistory L k p ∧ q<(carrier L k).terminal p then
    timeWeight L ell C k p*BaselineAssignmentScale.total L P k p A0 ν
      (fun j=>sharpConstant P d*(targets L k p (leafIndex k (fun i=>i) j))^((P.exponent-1)/4)) else 0

theorem gainDensity_measurable (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q A0 ν : ℝ) : Measurable (gainDensity L P d ell C k q A0 ν) := by
  apply Measurable.ite (activeHistory_measurableSet L k q)
  · refine (FixedHistoryTimeFactors.timeWeight_measurable L ell C k).mul
      (BaselineAssignmentScale.total_variable_measurable L P k id measurable_id A0 ν _ ?_)
    apply Measurable.of_eval
    intro j
    exact measurable_const.mul
      (((carrier L k).observations.target_measurable (leafIndex k (fun i=>i) j)).pow_const ((P.exponent-1)/4))
  · exact measurable_const

theorem gainDensity_nonneg (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j)
    (k : ℕ) (q A0 ν : ℝ) (p : History HeatCircle k) : 0≤gainDensity L P d ell C k q A0 ν p := by
  unfold gainDensity
  split_ifs with h
  · exact mul_nonneg (timeWeight_nonneg L hell C hC k p h.1)
      (BaselineAssignmentScale.total_nonneg L P k p A0 ν _)
  · exact le_rfl

/-- The actual erased-leaf sharp input density has fresh degree3/4 and
the SAME full original assignment/root time scale as the original word. -/
theorem gainDensity_le (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j)
    (k : ℕ) {q : ℝ} (hq0 : 0≤q) (A0 ν : ℝ) (p : History HeatCircle k) :
    gainDensity L P d ell C k q A0 ν p≤
      inputConstant P d k*totalIntegrand L P ell C k q (3/4:ℝ) A0 ν p := by
  by_cases hp : StrictHistory L k p ∧ q<(carrier L k).terminal p
  · rw [gainDensity,ite_eq_left hp,totalIntegrand,ite_eq_left hp]
    have hh := BaselineAssignmentScale.restored_total_gain L P d k p q A0 ν (sub_pos.mpr hp.2)
      (fun j=>OmittedTimeFactor.fresh_gap_le_leaf_age L k p q hq0 j)
    have hb := mul_le_mul_of_nonneg_left hh (timeWeight_nonneg L hell C hC k p hp.1)
    convert! hb using 1 <;> dsimp only [inputConstant] <;> norm_num <;> ring
  · simp only [gainDensity,totalIntegrand,ite_eq_right hp,mul_zero,le_refl]

/-- Actual old-time integration of the complete baseline input scale,
under the original restricted product measure and retaining all original
root clips, rough-block minima, empty-leaf full ages and root masses. -/
theorem gain_old_time_bound (P : CanonicalCovariance.ProfileParameters) (d : CircleL2)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ)
    {q A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) :
    Integrable (fun t=>gainDensity L P d ell C k q A0 ν (anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,gainDensity L P d ell C k q A0 ν (anchor k t)
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
        inputConstant P d k*oldTimeBudget P ell C k T q (3/4:ℝ) A0 ν := by
  have hh := total_old_time_budget L P T hT hell C hC k hqbase hqT hTH
    (by norm_num : (0:ℝ)<3/4) (by norm_num : (3/4:ℝ)≤1) hA0 hν
  have hm := (gainDensity_measurable L P d ell C k q A0 ν).comp (anchor_measurable k)
  have hdom (t : Fin k→ℝ) := gainDensity_le L P d hell C hC k (R.base_nonneg.trans hqbase) A0 ν (anchor k t)
  have hi := (hh.1.const_mul (inputConstant P d k)).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun t=>by
      dsimp only [Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (gainDensity_nonneg L P d hell C hC k q A0 ν _)]
      exact hdom t))
  refine ⟨hi,(integral_mono hi (hh.1.const_mul _) hdom).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hh.2 (inputConstant_nonneg P d k)

end SHE.BaselineTimeLedger
