module

public import SHE.TwoChannelMomentBracket
public import SHE.NativeHeatPointMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeTwoChannelMoments
open MeasureTheory StoppedFourier FiniteHaar PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal
local instance nativeTwoChannelMoments_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance nativeTwoChannelMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeTwoChannelMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell₀ M₀ ell₁ M₁ : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell₁ : 0 < ell₁) (hM₁ : 0 ≤ M₁)
variable (f₁ : ℝ≥0 × Ω → EllipticField ell₁ M₁) (hf₁ : StronglyMeasurable[𝓕.predictable] f₁)
variable {T : ℝ} (hT : (h : ℝ) ≤ T) (x : HeatCircle)

def input : Process (E := Both RealHaarInput) 𝓕 μ h :=
  TwoChannelItoRows.block 𝓕 μ h
    (NativeObservationEndpoint.process 𝓕 μ h hell₀ hM₀ f₀ hf₀ hT x)
    (NativeObservationEndpoint.process 𝓕 μ h hell₁ hM₁ f₁ hf₁ hT x)

theorem bracket_bound (hh : (h : ℝ) ≤ 1) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖input 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x (s, ω)‖ ^ 2) ∂timeMeasure h) ≤
      ENNReal.ofReal (ProfileVariance.upperConstant * (M₀ + M₁) * (h : ℝ) ^ (1 / 2 : ℝ)) := by
  have h0 := NativeHeatPointBracket.bracket_bound 𝓕 μ hh hell₀ hM₀ f₀ hf₀ hT x
  have h1 := NativeHeatPointBracket.bracket_bound 𝓕 μ hh hell₁ hM₁ f₁ hf₁ hT x
  have hb := TwoChannelMomentBracket.bracket_block_bound 𝓕 μ h
    (NativeObservationEndpoint.process 𝓕 μ h hell₀ hM₀ f₀ hf₀ hT x)
    (NativeObservationEndpoint.process 𝓕 μ h hell₁ hM₁ f₁ hf₁ hT x)
    (mul_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le hM₀) (Real.rpow_nonneg h.2 _))
    (mul_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le hM₁) (Real.rpow_nonneg h.2 _)) h0 h1
  have he : ProfileVariance.upperConstant * M₀ * (h : ℝ) ^ (1 / 2 : ℝ) +
      ProfileVariance.upperConstant * M₁ * (h : ℝ) ^ (1 / 2 : ℝ) =
      ProfileVariance.upperConstant * (M₀ + M₁) * (h : ℝ) ^ (1 / 2 : ℝ) := by ring
  filter_upwards [hb] with ω hω
  exact hω.trans_eq (congrArg ENNReal.ofReal he)

def value (I : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h) : Lp ℝ 2 μ :=
  I.integral (input 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x)

/-- Native two-channel moments use the actual block integral directly;
no conversion to a total-variance Haar factor or Brownian identification
is needed for this analytic estimate. -/
theorem moment (hh : (h : ℝ) ≤ 1)
    (I : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B) :
    (∫⁻ ω, ENNReal.ofReal
      (‖value 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x I ω‖ ^ (2 * p)) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * (ProfileVariance.upperConstant * (M₀ + M₁)) ^ p *
        (h : ℝ) ^ ((p : ℝ) / 2)) := by
  have hK : 0 ≤ ProfileVariance.upperConstant * (M₀ + M₁) * (h : ℝ) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (add_nonneg hM₀ hM₁)) (Real.rpow_nonneg h.2 _)
  have hb := StandardTerminalBDGPower.moment_of_bracket_bound I hBDG
    (input 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x) hK
    (bracket_bound 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x hh)
  apply hb.trans_eq
  congr 1
  rw [mul_pow, ← Real.rpow_mul_natCast (x := (h : ℝ)) h.2 (1 / 2 : ℝ) p]
  rw [show (1 / 2 : ℝ) * p = (p : ℝ) / 2 by ring]
  ring

theorem moment_on_initial_event (hh : (h : ℝ) ≤ 1)
    (I : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalConditionalBDGPower p I B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 0] A) :
    (∫⁻ ω in A, ENNReal.ofReal
      (‖value 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x I ω‖ ^ (2 * p)) ∂μ) ≤
      ENNReal.ofReal ((B : ℝ) * (ProfileVariance.upperConstant * (M₀ + M₁)) ^ p *
        (h : ℝ) ^ ((p : ℝ) / 2)) * μ A := by
  have hK : 0 ≤ ProfileVariance.upperConstant * (M₀ + M₁) * (h : ℝ) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (add_nonneg hM₀ hM₁)) (Real.rpow_nonneg h.2 _)
  have hb := StandardTerminalConditionalBDGPower.moment_of_bracket_bound I hBDG A hA
    (input 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x) hK
    (bracket_bound 𝓕 μ h hell₀ hM₀ f₀ hf₀ hell₁ hM₁ f₁ hf₁ hT x hh)
  have he : (B : ℝ) * (ProfileVariance.upperConstant * (M₀ + M₁) * (h : ℝ) ^ (1 / 2 : ℝ)) ^ p =
      (B : ℝ) * (ProfileVariance.upperConstant * (M₀ + M₁)) ^ p * (h : ℝ) ^ ((p : ℝ) / 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (x := (h : ℝ)) h.2 (1 / 2 : ℝ) p]
    rw [show (1 / 2 : ℝ) * p = (p : ℝ) / 2 by ring]
    ring
  rw [he] at hb
  exact hb

end SHE.NativeTwoChannelMoments
