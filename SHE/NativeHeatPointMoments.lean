module

public import SHE.NativeHeatPointBracket
public import SHE.NativePointMoments

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.NativeHeatPointMoments
open MeasureTheory StoppedFourier FiniteHaar PredictableL2
open scoped NNReal ENNReal
local instance nativeHeatPointMoments_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance nativeHeatPointMoments_finiteExponent : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [MeasurableSpace Ω]

def value (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    {T : ℝ} (hT : (h : ℝ) ≤ T) (x : HeatCircle) : Lp ℝ 2 μ :=
  I.integral (NativeObservationEndpoint.process 𝓕 μ h hell hM f hf hT x)

/-- Arbitrary further heat observation, all fixed even moments, and the
same quarter-time physical increment scale uniformly in the target age. -/
theorem moment (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {h : ℝ≥0} (hh : (h : ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B)
    {T : ℝ} (hT : (h : ℝ) ≤ T) (x : HeatCircle) :
    (∫⁻ ω, ENNReal.ofReal (‖value 𝓕 μ h hell hM f hf I hT x ω‖ ^ (2 * p)) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * (ProfileVariance.upperConstant * M) ^ p *
        (h : ℝ) ^ ((p : ℝ) / 2)) := by
  have hK : 0 ≤ ProfileVariance.upperConstant * M * (h : ℝ) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le hM) (Real.rpow_nonneg h.2 _)
  have hb := StandardTerminalBDGPower.moment_of_bracket_bound I hBDG
    (NativeObservationEndpoint.process 𝓕 μ h hell hM f hf hT x) hK
    (NativeHeatPointBracket.bracket_bound 𝓕 μ hh hell hM f hf hT x)
  apply hb.trans_eq
  congr 1
  rw [mul_pow, ← Real.rpow_mul_natCast (x := (h : ℝ)) h.2 (1 / 2 : ℝ) p]
  rw [show (1 / 2 : ℝ) * p = (p : ℝ) / 2 by ring]
  ring

theorem memLp (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {h : ℝ≥0} (hh : (h : ℝ) ≤ 1)
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (I : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    {p : ℕ} (hp : 0 < p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B)
    {T : ℝ} (hT : (h : ℝ) ≤ T) (x : HeatCircle) :
    MemLp (value 𝓕 μ h hell hM f hf I hT x) (2 * p : ℕ) μ :=
  NativePointMoments.memLp_of_even_moment (Lp.aestronglyMeasurable _) hp
    (moment 𝓕 μ hh hell hM f hf I p B hBDG hT x)

end SHE.NativeHeatPointMoments
