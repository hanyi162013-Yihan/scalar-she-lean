module

public import SHE.NativePastHybridInput
public import SHE.NativeHybridMoments
public import SHE.StandardTerminalPastLocality
public import SHE.RealMomentBound
public import SHE.FiniteMomentFractional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.NativePastHybridMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 StoppedFourier FiniteHaar
  OrthogonalItoChannels NativePastHybridInput ProfileVariance
open scoped NNReal ENNReal
local instance nativePastHybridMoments_period : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell₀ M₀ ell M : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell : 0 < ell) (hM : 0 ≤ M)
variable (fU fV : ℝ≥0 × Ω → EllipticField ell M)
variable (hfU : StronglyMeasurable[𝓕.predictable] fU) (hfV : StronglyMeasurable[𝓕.predictable] fV)
variable (v q : ℝ≥0) {T : ℝ} (hT : (q : ℝ) < T) (x : HeatCircle)
variable {Λ θ : ℝ} (hΛ : 0 ≤ Λ) (hθ : |θ| ≤ 1)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)

def value : Lp ℝ 2 μ :=
  J.integral (NativePastHybridInput.input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV v q hT x hΛ hθ)

abbrev momentConstant := NativeHybridMoments.momentConstant

theorem moment_on_past_event (hlocal : StandardTerminalPastLocality J) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1) (p : ℕ) (hp : 0<p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p J B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫⁻ ω in A,ENNReal.ofReal
      (‖value 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV v q hT x hΛ hθ J ω‖^(2*p)) ∂μ) ≤
      ENNReal.ofReal (momentConstant p B M₀ M*((q:ℝ)-(v:ℝ))^((p : ℝ)/2))*μ A := by
  have hK : 0 ≤ upperConstant*(2*M₀+10*M)*((q:ℝ)-(v:ℝ))^(1/2 : ℝ) :=
    mul_nonneg (mul_nonneg upperConstant_pos.le (by positivity)) (rpow_nonneg (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _)
  have hb := StandardTerminalPastLocality.moment_of_bracket_bound J hlocal hp hBDG v A hA
    (NativeHybridInput.input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ) hK
    (NativePastHybridInput.bracket_bound 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV v q hT x hΛ hθ hvq hqH hspan)
  apply hb.trans_eq
  congr 2
  unfold momentConstant NativeHybridMoments.momentConstant
  have ht : (((q:ℝ)-(v:ℝ))^(1/2 : ℝ))^p = ((q:ℝ)-(v:ℝ))^((p : ℝ)/2) := by
    calc
      _ = ((q:ℝ)-(v:ℝ))^((1/2 : ℝ)*(p : ℝ)) :=
        (Real.rpow_mul_natCast (x := ((q:ℝ)-(v:ℝ))) (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) (1/2 : ℝ) p).symm
      _ = _ := congrArg (fun t : ℝ => ((q:ℝ)-(v:ℝ))^t) (by ring)
  rw [mul_pow,ht]
  ring

theorem fractional_moment_on_past_event (hlocal : StandardTerminalPastLocality J) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (p : ℕ) (hp : 0<p) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    let Y := value 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV v q hT x hΛ hθ J
    Integrable (fun ω => |Y ω|^(((2*p:ℕ):ℝ)*β)) (μ.restrict A) ∧
      (∫ ω in A,|Y ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2)*μ.real A := by
  intro Y
  have hC : 0≤momentConstant p B M₀ M :=
    mul_nonneg B.2 (pow_nonneg (mul_nonneg upperConstant_pos.le (by positivity)) _)
  have hb := moment_on_past_event 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV
    v q hT x hΛ hθ J hlocal hvq hqH hspan p hp B hBDG A hA
  have hb0 : (∫⁻ ω,ENNReal.ofReal (‖Y ω‖^(((2*p:ℕ):ℝ))) ∂μ.restrict A)≤
      ENNReal.ofReal (momentConstant p B M₀ M*((q:ℝ)-(v:ℝ))^((p:ℝ)/2))*(μ.restrict A) Set.univ := by
    simpa only [Real.rpow_natCast,Measure.restrict_apply_univ] using hb
  have hh := FiniteMomentFractional.moment_fraction_mass
    ((Lp.aestronglyMeasurable Y).restrict (s:=A)) hβ hβ1
    (mul_nonneg hC (rpow_nonneg (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _)) hb0
  have he : (momentConstant p B M₀ M*((q:ℝ)-(v:ℝ))^((p:ℝ)/2))^β=
      (momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2) := by
    calc
      _=(momentConstant p B M₀ M)^β*(((q:ℝ)-(v:ℝ))^((p:ℝ)/2))^β :=
        Real.mul_rpow (z:=β) hC (rpow_nonneg (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _)
      _=(momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^(((p:ℝ)/2)*β) :=
        congrArg (fun z => (momentConstant p B M₀ M)^β*z) (Real.rpow_mul (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _ _).symm
      _=_ := congrArg (fun z => (momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^z) (by ring)
  erw [he,Measure.restrict_apply_univ] at hh
  have hK : 0≤(momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2) :=
    mul_nonneg (rpow_nonneg hC _) (rpow_nonneg (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _)
  have hmass : ENNReal.ofReal ((momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2))*μ A=
      ENNReal.ofReal ((momentConstant p B M₀ M)^β*((q:ℝ)-(v:ℝ))^((p:ℝ)*β/2)*μ.real A) := by
    rw [ENNReal.ofReal_mul hK,ofReal_measureReal]
  rw [hmass] at hh
  have hr := RealMomentBound.integral_bound (μ.restrict A) _
    ((((Lp.aestronglyMeasurable Y).restrict (s:=A)).norm.aemeasurable.pow_const _).aestronglyMeasurable)
    (fun _ => rpow_nonneg (norm_nonneg _) _) (mul_nonneg hK measureReal_nonneg) hh
  convert! hr using 1

end SHE.NativePastHybridMoments
