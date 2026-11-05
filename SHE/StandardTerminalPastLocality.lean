module

public import SHE.PastItoInputs
public import SHE.StandardTerminalBDGPower

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE
open MeasureTheory Set PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

/-- Ordinary deterministic-past event pullout for the SAME full-horizon
Ito integral. This is an explicit component of accepted stochastic
integration package1; it is not a consequence claimed for the weaker
linear-isometry/adaptedness/centering structure alone. No heat, nonlinear
SPDE, random profile or restart identity is included in this input. -/
def StandardTerminalPastLocality
    (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H) : Prop :=
  ∀ (v : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) (u : Process (E := C) 𝓕 μ H),
    I.integral (eventProcess 𝓕 μ H v A hA u) =ᵐ[μ]
      A.indicator (I.integral (post 𝓕 μ H v u))

namespace StandardTerminalPastLocality
variable [SFinite μ]

/-- Conditional BDG on any deterministic past event is DERIVED from
ordinary full-horizon BDG and event pullout. No new conditional stochastic
estimate or independently restarted integral is assumed. -/
theorem conditional_bdg (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H)
    (hlocal : StandardTerminalPastLocality I) {p : ℕ} (hp : 0<p)
    {B : ℝ≥0} (hBDG : StandardTerminalBDGPower p I B)
    (v : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) (u : Process (E := C) 𝓕 μ H) :
    (∫⁻ ω in A,ENNReal.ofReal (‖I.integral (post 𝓕 μ H v u) ω‖^(2*p)) ∂μ)≤
      (B:ℝ≥0∞)*(∫⁻ ω in A,
        (∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H)^p ∂μ) := by
  have hp2 : 2*p≠0 := Nat.mul_ne_zero (by norm_num) hp.ne'
  have hL : (∫⁻ ω,ENNReal.ofReal (‖I.integral (eventProcess 𝓕 μ H v A hA u) ω‖^(2*p)) ∂μ)=
      ∫⁻ ω in A,ENNReal.ofReal (‖I.integral (post 𝓕 μ H v u) ω‖^(2*p)) ∂μ := by
    calc
      _ = ∫⁻ ω,A.indicator (fun ω => ENNReal.ofReal (‖I.integral (post 𝓕 μ H v u) ω‖^(2*p))) ω ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlocal v A hA u] with ω hω
        rw [hω]
        by_cases ha : ω∈A <;> simp [ha,hp2]
      _ = _ := lintegral_indicator (𝓕.le v A hA) _
  have hR : (∫⁻ ω,(∫⁻ s,ENNReal.ofReal (‖eventProcess 𝓕 μ H v A hA u (s,ω)‖^2) ∂timeMeasure H)^p ∂μ)=
      ∫⁻ ω in A,(∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H)^p ∂μ := by
    calc
      _ = ∫⁻ ω,A.indicator (fun ω => (∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H)^p) ω ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [event_bracket_ae 𝓕 μ H v A hA u] with ω hω
        rw [hω]
        by_cases ha : ω∈A <;> simp [ha,hp.ne']
      _ = _ := lintegral_indicator (𝓕.le v A hA) _
  have hh := hBDG (eventProcess 𝓕 μ H v A hA u)
  rw [hL,hR] at hh
  exact hh

theorem moment_of_bracket_bound (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H)
    (hlocal : StandardTerminalPastLocality I) {p : ℕ} (hp : 0<p)
    {B : ℝ≥0} (hBDG : StandardTerminalBDGPower p I B)
    (v : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) (u : Process (E := C) 𝓕 μ H)
    {K : ℝ} (hK : 0≤K)
    (hbr : ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H)≤ENNReal.ofReal K) :
    (∫⁻ ω in A,ENNReal.ofReal (‖I.integral (post 𝓕 μ H v u) ω‖^(2*p)) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*K^p)*μ A := by
  have hh : (∫⁻ ω in A,(∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H)^p ∂μ)≤
      (ENNReal.ofReal K)^p*μ A := by
    have hi := lintegral_mono_ae ((ae_restrict_of_ae (s := A) hbr).mono
      (fun _ hω => pow_le_pow_left₀ (by simp) hω p))
    simpa only [lintegral_const,Measure.restrict_apply_univ] using hi
  calc
    _ ≤ (B:ℝ≥0∞)*(∫⁻ ω in A,(∫⁻ s,ENNReal.ofReal (‖post 𝓕 μ H v u (s,ω)‖^2) ∂timeMeasure H)^p ∂μ) :=
      conditional_bdg I hlocal hp hBDG v A hA u
    _ ≤ (B:ℝ≥0∞)*((ENNReal.ofReal K)^p*μ A) := mul_le_mul_right hh _
    _ = _ := by
      rw [← ENNReal.ofReal_pow hK,← mul_assoc,
        show (B:ℝ≥0∞)=ENNReal.ofReal (B:ℝ) by simp]
      congr 1
      exact (ENNReal.ofReal_mul B.2).symm

end StandardTerminalPastLocality
end SHE
