module

public import SHE.NativeHybridInput
public import SHE.RealMomentBound
public import SHE.FiniteMomentFractional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.NativeHybridMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 StoppedFourier FiniteHaar
  OrthogonalItoChannels NativeHybridInput ProfileVariance
open scoped NNReal ENNReal
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell₀ M₀ ell M : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell : 0 < ell) (hM : 0 ≤ M)
variable (fU fV : ℝ≥0 × Ω → EllipticField ell M)
variable (hfU : StronglyMeasurable[𝓕.predictable] fU) (hfV : StronglyMeasurable[𝓕.predictable] fV)
variable (q : ℝ≥0) {T : ℝ} (hT : (q : ℝ) < T) (x : HeatCircle)
variable {Λ θ : ℝ} (hΛ : 0 ≤ Λ) (hθ : |θ| ≤ 1)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)

def value : Lp ℝ 2 μ :=
  J.integral (input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ)

def momentConstant (p : ℕ) (B : ℝ≥0) (M₀ M : ℝ) : ℝ :=
  (B : ℝ)*(upperConstant*(2*M₀+10*M))^p

theorem moment (hqH : q ≤ H) (hq1 : (q : ℝ) ≤ 1) (p : ℕ) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p J B) :
    (∫⁻ ω,ENNReal.ofReal (‖value 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ J ω‖^(2*p)) ∂μ) ≤
      ENNReal.ofReal (momentConstant p B M₀ M*(q : ℝ)^((p : ℝ)/2)) := by
  have hK : 0 ≤ upperConstant*(2*M₀+10*M)*(q : ℝ)^(1/2 : ℝ) :=
    mul_nonneg (mul_nonneg upperConstant_pos.le (by positivity)) (rpow_nonneg q.2 _)
  have hb := StandardTerminalBDGPower.moment_of_bracket_bound J hBDG
    (input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ) hK
    (NativeHybridInput.bracket_bound 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ hqH hq1)
  apply hb.trans_eq
  congr 1
  unfold momentConstant
  have ht : ((q : ℝ)^(1/2 : ℝ))^p = (q : ℝ)^((p : ℝ)/2) := by
    calc
      _ = (q : ℝ)^((1/2 : ℝ)*(p : ℝ)) :=
        (Real.rpow_mul_natCast (x := (q : ℝ)) q.2 (1/2 : ℝ) p).symm
      _ = _ := congrArg (fun t : ℝ => (q : ℝ)^t) (by ring)
  rw [mul_pow,ht]
  ring

/-- The same accepted conditional BDG input controls the literal hybrid
on every initial event, with its true event mass and the same full J. -/
theorem moment_on_initial_event (hqH : q ≤ H) (hq1 : (q : ℝ) ≤ 1) (p : ℕ) (B : ℝ≥0)
    (hBDG : StandardTerminalConditionalBDGPower p J B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 0] A) :
    (∫⁻ ω in A,ENNReal.ofReal
      (‖value 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ J ω‖^(2*p)) ∂μ) ≤
      ENNReal.ofReal (momentConstant p B M₀ M*(q : ℝ)^((p : ℝ)/2))*μ A := by
  have hK : 0 ≤ upperConstant*(2*M₀+10*M)*(q : ℝ)^(1/2 : ℝ) :=
    mul_nonneg (mul_nonneg upperConstant_pos.le (by positivity)) (rpow_nonneg q.2 _)
  have hb := StandardTerminalConditionalBDGPower.moment_of_bracket_bound J hBDG A hA
    (input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ) hK
    (NativeHybridInput.bracket_bound 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ hqH hq1)
  apply hb.trans_eq
  congr 2
  unfold momentConstant
  have ht : ((q : ℝ)^(1/2 : ℝ))^p = (q : ℝ)^((p : ℝ)/2) := by
    calc
      _ = (q : ℝ)^((1/2 : ℝ)*(p : ℝ)) :=
        (Real.rpow_mul_natCast (x := (q : ℝ)) q.2 (1/2 : ℝ) p).symm
      _ = _ := congrArg (fun t : ℝ => (q : ℝ)^t) (by ring)
  rw [mul_pow,ht]
  ring

/-- The real fractional displacement moment required by rough marked
leaves follows from the actual hybrid BDG moment, without a Gaussian or
independence hypothesis on the current state. -/
theorem fractional_moment (hqH : q ≤ H) (hq1 : (q : ℝ) ≤ 1) (p : ℕ) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p J B) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    let Y := value 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ J
    Integrable (fun ω => |Y ω|^(((2*p : ℕ) : ℝ)*β)) μ ∧
      (∫ ω,|Y ω|^(((2*p : ℕ) : ℝ)*β) ∂μ) ≤
        (momentConstant p B M₀ M)^β*(q : ℝ)^((p : ℝ)*β/2) := by
  intro Y
  have hC : 0 ≤ momentConstant p B M₀ M :=
    mul_nonneg B.2 (pow_nonneg (mul_nonneg upperConstant_pos.le (by positivity)) _)
  have h := FractionalMoment.moment_fraction (q := ((2*p : ℕ) : ℝ))
    (C := momentConstant p B M₀ M*(q : ℝ)^((p : ℝ)/2)) (Lp.aestronglyMeasurable Y) hβ hβ1
    (mul_nonneg hC (rpow_nonneg q.2 _))
    (by simpa only [Real.rpow_natCast] using
      moment 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ J hqH hq1 p B hBDG)
  have he : (momentConstant p B M₀ M*(q : ℝ)^((p : ℝ)/2))^β =
      (momentConstant p B M₀ M)^β*(q : ℝ)^((p : ℝ)*β/2) := by
    calc
      _ = (momentConstant p B M₀ M)^β*((q : ℝ)^((p : ℝ)/2))^β :=
        Real.mul_rpow (z := β) hC (rpow_nonneg q.2 ((p : ℝ)/2))
      _ = (momentConstant p B M₀ M)^β*(q : ℝ)^(((p : ℝ)/2)*β) :=
        congrArg (fun t => (momentConstant p B M₀ M)^β*t)
          (Real.rpow_mul q.2 ((p : ℝ)/2) β).symm
      _ = _ := congrArg (fun t => (momentConstant p B M₀ M)^β*(q : ℝ)^t) (by ring)
  rw [he] at h
  have hh := RealMomentBound.integral_bound μ _
    ((Lp.aestronglyMeasurable Y).norm.aemeasurable.pow_const _).aestronglyMeasurable
    (fun _ => rpow_nonneg (norm_nonneg _) _)
    (mul_nonneg (rpow_nonneg hC _) (rpow_nonneg q.2 _)) h
  convert! hh using 1

end SHE.NativeHybridMoments
