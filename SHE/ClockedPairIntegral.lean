module

public import SHE.ClockedPairFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ClockedPairIntegral
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0) (hh : (h:ℝ)≤1)
variable {Λ ell M : ℝ} (hΛ : 0≤Λ) (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M)
variable (hf : StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] f)

theorem time_le {t : ℝ≥0} (ht : t≤c*h) : (clock c hc).symm t≤h := by
  rw [← ClockedHaarIntegral.unitTime_eq c hc h ht]
  exact min_le_left _ _

/-- Equality of the actual predictable integrands, rather than merely
an equality of formal covariance kernels. -/
theorem unitInput_eq (g : ℝ≥0×Ω→EllipticField ((c:ℝ)*ell) ((c:ℝ)*M))
    (hg : StronglyMeasurable[𝓕.predictable] g)
    (hfg : ClockedHaarIntegral.unitField c hc f=g) (t : ℝ≥0) (ht : t≤c*h) :
    ClockedHaarIntegral.unitInput 𝓕 μ c hc h hh hΛ hell hM f hf t=
      DampedFixedIntegral.input 𝓕 μ h hh (mul_nonneg c.2 hΛ) (mul_pos hc hell)
        (mul_nonneg c.2 hM) g hg ((clock c hc).symm t) (time_le c hc h ht) := by
  unfold ClockedHaarIntegral.unitInput
  simp only [ClockedHaarIntegral.unitTime_eq c hc h ht]
  exact DampedFixedIntegral.input_congr 𝓕 μ h hh (mul_nonneg c.2 hΛ) (mul_pos hc hell)
    (mul_nonneg c.2 hM) _ _ _ _ (Filter.Eventually.of_forall (congrFun hfg)) _ _

theorem terminal_eq (g : ℝ≥0×Ω→EllipticField ((c:ℝ)*ell) ((c:ℝ)*M))
    (hg : StronglyMeasurable[𝓕.predictable] g)
    (hfg : ClockedHaarIntegral.unitField c hc f=g)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (t : ℝ≥0) (ht : t≤c*h) :
    (PredictableTimeDilation.integral 𝓕 μ c hc h I).integral
      (ClockedHaarIntegral.input 𝓕 μ c hc h hh hΛ hell hM f hf t)=
        DampedFixedIntegral.value 𝓕 μ h hh (mul_nonneg c.2 hΛ) (mul_pos hc hell)
          (mul_nonneg c.2 hM) g hg I ((clock c hc).symm t) (time_le c hc h ht) := by
  rw [ClockedHaarIntegral.integral_input,unitInput_eq 𝓕 μ c hc h hh hΛ hell hM f hf g hg hfg t ht]
  rfl

end SHE.ClockedPairIntegral
