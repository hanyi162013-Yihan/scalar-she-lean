module

public import SHEStochastic.ScalarLinearGrowthDriftField
public import SHEStochastic.ContinuousNormExit
public import SHE.IntegralEnergy
public import SHE.NativeHeatObservation
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedDriftConvolution
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω : Type*} {H : ℝ≥0} (b : ScalarLinearGrowthDriftField.Data H)
  (W : ℝ≥0 → Ω → RealL2) (a : ℝ≥0 → Ω → ℝ)
  (N : ℕ) (ω : Ω)

local notation "τ" => ContinuousNormExit.exit W N

/-- Stopping multiplies the original Borel drift by its actual
pre-exit indicator and the supplied time/path multiplier. -/
def input (s : ℝ≥0) : RealL2 :=
  if (s : WithTop ℝ≥0) < τ ω then a s ω • ScalarLinearGrowthDriftField.field b (s,W s ω) else 0

def convolution (T : ℝ≥0) : RealL2 :=
  ∫ s,NativeHeatObservation.heat ((T : ℝ)-(s : ℝ)) (input b W a N ω s) ∂timeMeasure T

theorem input_bound (ha : ∀ s,|a s ω|≤1) (s : ℝ≥0) :
    ‖input b W a N ω s‖^2 ≤
      if (s : WithTop ℝ≥0) < τ ω then 2*(b.growth : ℝ)^2*(1+‖W s ω‖^2) else 0 := by
  by_cases hs : (s : WithTop ℝ≥0) < τ ω
  · rw [input,ite_eq_left hs,ite_eq_left hs,norm_smul,mul_pow,Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) (ha s))).trans
      (ScalarLinearGrowthDriftField.field_norm_sq_le b (s,W s ω))
  · rw [input,ite_eq_right hs,ite_eq_right hs,norm_zero]
    norm_num

private theorem measurable_before :
    MeasurableSet {s : ℝ≥0 | (s : WithTop ℝ≥0) < τ ω} := by
  rcases eq_or_ne (τ ω) ⊤ with ht | ht
  · simp only [ht,WithTop.coe_lt_top,Set.ofPred_true,MeasurableSet.univ]
  · obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp ht
    simp only [←hr,WithTop.coe_lt_coe]
    exact measurableSet_Iio (a := r)

theorem input_measurable (hc : Continuous (fun s => W s ω)) (ha : Measurable (fun s => a s ω)) :
    Measurable (input b W a N ω) := by
  exact Measurable.ite (measurable_before W N ω)
    (ha.smul ((ScalarLinearGrowthDriftField.field_measurable b).comp
      (measurable_id.prodMk hc.measurable))) measurable_const

/-- The deterministic part of the stopped mild second-moment estimate
comes from the actual heat contraction and finite time mass. -/
theorem energy [MeasurableSpace Ω] (hc : ∀ ω,Continuous (fun s => W s ω))
    (ham : Measurable (fun s => a s ω)) (ha : ∀ s,|a s ω|≤1) (T : ℝ≥0) :
    ‖convolution b W a N ω T‖^2 ≤ (T : ℝ) *
      ∫ s, (if (s : WithTop ℝ≥0) < τ ω then 2*(b.growth : ℝ)^2*(1+‖W s ω‖^2) else 0)
        ∂timeMeasure T := by
  let h (s : ℝ≥0) := if (s : WithTop ℝ≥0) < τ ω then 2*(b.growth : ℝ)^2*(1+‖W s ω‖^2) else 0
  let v (s : ℝ≥0) := NativeHeatObservation.heat ((T : ℝ)-(s : ℝ)) (input b W a N ω s)
  have hv : StronglyMeasurable v := by
    have ht : Measurable (fun s : ℝ≥0 => ((T : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale) := by fun_prop
    have hB : StronglyMeasurable (input b W a N ω) :=
      (input_measurable b W a N ω (hc ω) ham).stronglyMeasurable
    let p (s : ℝ≥0) : ℝ × RealL2 :=
      (((T : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale,input b W a N ω s)
    have hp : StronglyMeasurable p := ht.stronglyMeasurable.prodMk hB
    have hh := RealHeat.continuous_realHeat_action.comp_stronglyMeasurable hp
    simpa only [v,p,NativeHeatObservation.heat,Function.comp_apply] using hh
  have hh : StronglyMeasurable h :=
    (Measurable.ite (measurable_before W N ω)
      (((hc ω).norm.measurable.pow_const 2).const_add 1 |>.const_mul (2*(b.growth : ℝ)^2))
      measurable_const).stronglyMeasurable
  have hh0 (s : ℝ≥0) : 0≤h s := by
    by_cases hs : (s : WithTop ℝ≥0) < τ ω
    · dsimp only [h]
      rw [ite_eq_left hs]
      positivity
    · simp only [h,ite_eq_right hs,le_refl]
  have hcap (s : ℝ≥0) : ‖h s‖≤2*(b.growth : ℝ)^2*(1+(N : ℝ)^2) := by
    rw [Real.norm_of_nonneg (hh0 s)]
    by_cases hs : (s : WithTop ℝ≥0) < τ ω
    · dsimp only [h]
      rw [ite_eq_left hs]
      have hn := (ContinuousNormExit.before_bound W hc N s ω hs).le
      gcongr
    · simp only [h,ite_eq_right hs]
      positivity
  have hI : Integrable h (timeMeasure T) :=
    Integrable.of_bound hh.aestronglyMeasurable _ (Filter.Eventually.of_forall hcap)
  have hV (s : ℝ≥0) : ‖v s‖^2≤h s :=
    (pow_le_pow_left₀ (norm_nonneg _) (RealHeat.realHeat_contraction
      (((T : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale) (input b W a N ω s)) 2).trans
        (input_bound b W a N ω ha s)
  have hM : MemLp v 2 (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
      (hI.mono' (hv.norm.pow 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact hV s))
  change ‖(∫ s,v s ∂timeMeasure T)‖^2 ≤ (T : ℝ)*(∫ s,h s ∂timeMeasure T)
  have hmass : (timeMeasure T).real univ=(T : ℝ) := by
    rw [Measure.real,timeMeasure_mass]
    exact ENNReal.toReal_ofReal (show (0 : ℝ) ≤ T from T.property)
  exact (IntegralEnergy.norm_integral_sq (timeMeasure T) v hM).trans
    (by
      rw [hmass]
      exact mul_le_mul_of_nonneg_left (integral_mono hM.norm.integrable_sq hI hV) T.property)

end SHEStochastic.ScalarStoppedDriftConvolution
