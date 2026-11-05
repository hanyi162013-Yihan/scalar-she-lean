module

public import SHEStochastic.BoundedFourierInput
public import SHEStochastic.PathIntegratedCovariance
public import SHEStochastic.StateDriverCovariance
public import SHEStochastic.NativeCrossCompensator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeFourierCompensatorValue
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

def diagonal : BoundedContinuousFunction RealL2 ℝ :=
  (StateNoiseCovariance.bounded haarAddCircle hβ hβ1.le hG hG (weight a n) (weight a n)
    B B B.property B.property hb hb).compContinuous ⟨NativePhysicalState.push, NativePhysicalState.push.continuous⟩

def mixed (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi))) : BoundedContinuousFunction RealL2 ℝ :=
  (StateDriverCovariance.bounded haarAddCircle hβ hβ1.le hG (weight a n) b B B.property hb).compContinuous
    ⟨NativePhysicalState.push, NativePhysicalState.push.continuous⟩

theorem diagonal_apply (u : RealL2) : diagonal hG hβ hβ1 B hb a n u =
    ‖StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight a n) (NativePhysicalState.push u)‖^2 := by
  change inner ℝ
    (StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight a n) (NativePhysicalState.push u))
    (StateNoiseCovariance.row haarAddCircle hβ hβ1.le hG (weight a n) (NativePhysicalState.push u)) = _
  exact real_inner_self_eq_norm_sq _

theorem diagonal_difference {K : ℝ → V} {D : ℝ≥0} (hK : HolderWith D β K)
    (hKb : ∀ z, ‖K z‖ ≤ B) (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ z, ‖G z-K z‖ ≤ δ) :
    ‖diagonal hG hβ hβ1 B hb a n-diagonal hK hβ hβ1 B hKb a n‖ ≤
      ‖weight a n‖*‖weight a n‖*((B : ℝ)+B)*δ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro u
  exact StateNoiseCovarianceStability.value_difference haarAddCircle hβ hβ1.le hG hK
    (weight a n) (weight a n) B B δ B.property B.property hδ hb hKb hclose (NativePhysicalState.push u)

theorem mixed_difference {K : ℝ → V} {D : ℝ≥0} (hK : HolderWith D β K)
    (hKb : ∀ z, ‖K z‖ ≤ B) (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi)))
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ z, ‖G z-K z‖ ≤ δ) :
    ‖mixed hG hβ hβ1 B hb a n b-mixed hK hβ hβ1 B hKb a n b‖ ≤ ‖weight a n‖*δ*‖b‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro u
  exact StateDriverCovariance.difference haarAddCircle hβ hβ1.le hG hK (weight a n) b δ hδ hclose
    (NativePhysicalState.push u)

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))

/-- The native square compensator is the literal continuous path
functional used when taking the weak approximation limit. -/
theorem energy_ae : ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ H →
    PredictableBracket.energy (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n) T sample =
      ∫ s in (0 : ℝ)..(T : ℝ), Real.exp (s*(2*(n : ℝ)^2))*
        diagonal hG hβ hβ1 B hb a n (W s.toNNReal sample) := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae
    (BoundedFourierInput.input_ae F μ H W hW hG hβ hβ1 B hb a n)
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with sample hrow T hT
  change (∫ s, (Set.Iio T).indicator
    (fun s ↦ ‖BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n (s,sample)‖^2) s
      ∂PredictableL2.timeMeasure H) = _
  rw [timeMeasure_eq] at hrow ⊢
  calc
    _ = ∫ s, (Set.Iio T).indicator (fun s : ℝ≥0 ↦
        Real.exp ((s : ℝ)*(2*(n : ℝ)^2))*diagonal hG hβ hβ1 B hb a n (W s sample)) s
          ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
      apply integral_congr_ae
      filter_upwards [hrow] with s hs
      by_cases ht : s < T
      · simp only [Set.indicator_apply, Set.mem_Iio, ht, ite_true]
        dsimp only [Prod.swap] at hs
        rw [hs, BoundedFourierInput.row, norm_smul, Real.norm_eq_abs]
        dsimp [FourierHeatInput.multiplier]
        rw [abs_of_pos (Real.exp_pos _), min_eq_left (show (s : ℝ) ≤ H from ht.le.trans hT),
          mul_pow, diagonal_apply, pow_two (Real.exp _), ← Real.exp_add]
        congr 1
        congr 1
        ring
      · simp only [Set.indicator_apply, Set.mem_Iio, ht, ite_false]
    _ = _ := by
      simpa only [Real.toNNReal_coe] using PathIntegratedCovariance.clock_before H T hT
        (fun s ↦ Real.exp (s*(2*(n : ℝ)^2))*diagonal hG hβ hβ1 B hb a n (W s.toNNReal sample))

theorem mixed_ae [SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))]
    (b : Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :
    ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ H →
      NativeCrossCompensator.value
        (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)
        (RotatedCylindricalCoordinates.constant F μ H b) T sample =
      ∫ s in (0 : ℝ)..(T : ℝ), Real.exp (s*(n : ℝ)^2)*
        mixed hG hβ hβ1 B hb a n b (W s.toNNReal sample) := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  let u := BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n
  let v := RotatedCylindricalCoordinates.constant F μ H b
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae
    ((BoundedFourierInput.input_ae F μ H W hW hG hβ hβ1 B hb a n).and
      (RotatedCylindricalCoordinates.constant_ae F μ H b))
  filter_upwards [NativeCrossCompensator.value_ae u v, Measure.ae_ae_of_ae_prod hs]
    with sample hvalue hrow T hT
  rw [hvalue T]
  rw [timeMeasure_eq] at hrow ⊢
  calc
    _ = ∫ s, (Set.Iio T).indicator (fun s : ℝ≥0 ↦ Real.exp ((s : ℝ)*(n : ℝ)^2)*
        mixed hG hβ hβ1 B hb a n b (W s sample)) s
          ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
      apply integral_congr_ae
      filter_upwards [hrow] with s hs
      by_cases ht : s < T
      · simp only [Set.indicator_apply, Set.mem_Iio, ht, ite_true]
        dsimp only [Prod.swap] at hs
        change inner ℝ (u (s,sample)) (v (s,sample)) = _
        rw [hs.1, hs.2, BoundedFourierInput.row, real_inner_smul_left]
        dsimp [FourierHeatInput.multiplier]
        rw [min_eq_left (show (s : ℝ) ≤ H from ht.le.trans hT)]
        rfl
      · simp only [Set.indicator_apply, Set.mem_Iio, ht, ite_false]
    _ = _ := by
      simpa only [Real.toNNReal_coe] using PathIntegratedCovariance.clock_before H T hT
        (fun s ↦ Real.exp (s*(n : ℝ)^2)*mixed hG hβ hβ1 B hb a n b (W s.toNNReal sample))

end SHEStochastic.NativeFourierCompensatorValue
