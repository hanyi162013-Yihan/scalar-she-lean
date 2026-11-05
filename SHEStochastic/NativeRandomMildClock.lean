module

public import SHE.NativePairKernels
public import SHEStochastic.NativeSmoothRandomMildExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeRandomMildClock
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.FiniteHaar SHE.ContinuousHeatMild
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (hH : (H : ℝ) ≤ 1)
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ}
  (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
  (hm : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell cap hell hb))
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  (Z : Ω → StateL2) (U : ℝ≥0 → Ω → StateL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (hf : StronglyMeasurable[F.predictable]
    (coefficientFunction (ha.const_mul (NativeClock.rate : ℝ)) (mul_pos NativeClock.rate_pos hell)
      (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) U))

/-- The existing deterministic clock conversion also applies to random
initial data. The same constructed Haar kernel and integral are retained;
the initial term is converted sample by sample. -/
theorem mild
    (hmild : ∀ (t : ℝ≥0) (ht : t ≤ H), U t =ᵐ[μ] fun sample ↦
      RealHeat.realHeat (t : ℝ) (Z sample) +
        DampedFixedIntegral.value F μ H hH (Λ := 0) (by norm_num)
          (mul_pos NativeClock.rate_pos hell)
          (mul_nonneg NativeClock.rate.2 (hell.le.trans ((hb 0).1.trans (hb 0).2)))
          (coefficientFunction (ha.const_mul (NativeClock.rate : ℝ)) (mul_pos NativeClock.rate_pos hell)
            (HaarFieldScaling.scaled_bounds NativeClock.rate_pos hb) U) hf I t ht sample)
    (t : ℝ≥0) (ht : t ≤ NativeClock.rate*H) :
    NativePairClock.path U t =ᵐ[μ] fun sample ↦
      NativeHeatObservation.heat (t : ℝ) (Z sample) +
        (PredictableTimeDilation.integral F μ NativeClock.rate NativeClock.rate_pos H I).integral
          (NativePairClock.residualInput F μ H hH (Λ := 0) (by norm_num)
            ha hell hb hm U hU t) sample := by
  have hR := NativePairClock.residual_terminal_eq F μ H hH (Λ := 0) (by norm_num)
    ha hell hb hm U hU hf I t ht
  simp only [mul_zero] at hR
  filter_upwards [hmild (NativeClock.time t) (ClockedPairIntegral.time_le _ _ _ ht)] with sample hs
  change U (NativeClock.time t) sample = _
  have hHeat := congrArg (fun L : StateL2 →L[ℝ] StateL2 ↦ L (Z sample)) (NativeClock.heat_time t)
  exact hs.trans (congrArg₂ (fun x y : StateL2 ↦ x+y) hHeat
    (congrArg (fun v : Lp StateL2 2 μ ↦ v sample) hR).symm)

end SHEStochastic.NativeRandomMildClock
