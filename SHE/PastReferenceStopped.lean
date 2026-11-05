module

public import SHE.PastReferenceIntegral
public import SHE.PastReferenceInput
public import SHE.PastItoAlgebra
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastReferenceStopped
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier PastItoInputs PastReferenceBracket StoppedItoInputs
open scoped NNReal ENNReal
local instance pastReferenceStopped_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance pastReferenceStopped_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance pastReferenceStopped_instance3 : MeasurableSpace CircleL2 := borel _
local instance pastReferenceStopped_instance4 : BorelSpace CircleL2 := ⟨rfl⟩
local instance pastReferenceStopped_instance5 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance pastReferenceStopped_instance6 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ} (hΛ : 0≤Λ) (hκ : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (H v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data)
variable (hdi : Integrable (fun ω => ‖(data ω).2‖^2) μ)
local notation "Input" => input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi
local notation "Cref" => energyConstant P κ θ η ((b:ℝ)-(v:ℝ))

/-- The original FULL-terminal frozen-reference input stopped at the
current time. Its heat target remains b, even when current s<b. -/
def stopped (s : ℝ) : Process (E := RealHaarIntegrand.Columns) 𝓕 μ H :=
  stop 𝓕 μ H s Input
local notation "Stopped"=>stopped 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi
attribute [local irreducible] PastReferenceBracket.input

/-- Stopping the full-target frozen input preserves its exact post-v
support in the original full-horizon predictable input space. -/
theorem post_stopped (s : ℝ) : post 𝓕 μ H v (Stopped s)=Stopped s := by
  have hpi:=post_ae 𝓕 μ H v Input
  rw [PastReferenceBracket.post_input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi] at hpi
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (Stopped s),stop_ae 𝓕 μ H s Input,hpi] with p hp hs hi
  change post 𝓕 μ H v (Stopped s) p=(Stopped s) p
  rw [hp]
  by_cases hv : v<p.1
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    have hiz : Input p=0 := by simpa only [ite_eq_right hv] using hi
    change (0:RealHaarIntegrand.Columns)=stop 𝓕 μ H s Input p
    rw [hs]
    by_cases hm : p∈before (Ω := Ω) s
    · rw [indicator_of_mem hm,hiz]
    · rw [indicator_of_notMem hm]

/-- Every partial bracket is bounded by the true FULL-target frozen
reference bracket. The bound uses b-v, not the current elapsed s-v. -/
theorem stopped_bracket (s : ℝ) :
    ∀ᵐ ω ∂μ,(∫⁻ r,ENNReal.ofReal (‖Stopped s (r,ω)‖^2) ∂timeMeasure H)≤
      ENNReal.ofReal (Cref*‖(data ω).2‖^2) := by
  have he:=(Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae
    (stop_ae 𝓕 μ H s Input)
  filter_upwards [Measure.ae_ae_of_ae_prod he,
    PastReferenceBracket.input_bracket 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi] with ω hω hb
  refine le_trans ?_ hb
  apply lintegral_mono_ae
  filter_upwards [hω] with r hr
  change stop 𝓕 μ H s Input (r,ω)=(before s).indicator Input (r,ω) at hr
  change ENNReal.ofReal (‖stop 𝓕 μ H s Input (r,ω)‖^2)≤ENNReal.ofReal (‖Input (r,ω)‖^2)
  rw [hr]
  by_cases hm : (r,ω)∈before (Ω := Ω) s
  · rw [indicator_of_mem hm]
  · rw [indicator_of_notMem hm]
    simp only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),ENNReal.ofReal_zero]
    exact bot_le

/-- Conditional even moments of the actual stopped full-target
frozen reference integral, retaining the random past difference norm. -/
theorem moment_on_past_event (s : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := E) 𝓕 μ H)
    (hlocal : StandardTerminalPastLocality I) {p : ℕ} (hp : 0<p)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B)
    (hmoment : Integrable (fun ω => ‖(data ω).2‖^(2*p)) μ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    Integrable (fun ω => ‖I.integral (Stopped s) ω‖^(2*p)) (μ.restrict A) ∧
      (∫ ω in A,‖I.integral (Stopped s) ω‖^(2*p) ∂μ)≤
        (B:ℝ)*Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ) := by
  have hC : 0≤Cref := energyConstant_nonneg P hκ
    (sub_nonneg.mpr (by exact_mod_cast hvb.le)) θ η
  have hbr := stopped_bracket 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi s
  have hpow : (∫⁻ ω in A,(∫⁻ r,ENNReal.ofReal (‖Stopped s (r,ω)‖^2) ∂timeMeasure H)^p ∂μ)≤
      ENNReal.ofReal (Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ)) := by
    calc
      _ ≤ ∫⁻ ω in A,ENNReal.ofReal (Cref^p*‖(data ω).2‖^(2*p)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hbr] with ω hω
        have hh := pow_le_pow_left₀ (by simp) hω p
        rw [←ENNReal.ofReal_pow (mul_nonneg hC (sq_nonneg _)),mul_pow,←pow_mul] at hh
        exact hh
      _ = _ := by
        rw [←ofReal_integral_eq_lintegral_ofReal (hmoment.const_mul (Cref^p)).integrableOn
          (Filter.Eventually.of_forall (fun ω => mul_nonneg (pow_nonneg hC _) (pow_nonneg (norm_nonneg _) _))),
          integral_const_mul]
  have hh := StandardTerminalPastLocality.conditional_bdg I hlocal hp hBDG v A hA (Stopped s)
  rw [post_stopped 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi s] at hh
  have hbound : (∫⁻ ω in A,ENNReal.ofReal (‖I.integral (Stopped s) ω‖^(2*p)) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ)) := by
    calc
      _ ≤ _ := hh
      _ ≤ (B:ENNReal)*ENNReal.ofReal (Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ)) := mul_le_mul_right hpow _
      _ = _ := by
        rw [show (B:ENNReal)=ENNReal.ofReal (B:ℝ) by simp]
        have he : ENNReal.ofReal ((B:ℝ)*(Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ)))=
            ENNReal.ofReal (B:ℝ)*ENNReal.ofReal (Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ)) :=
          ENNReal.ofReal_mul B.2
        rw [←he]
        congr 1
        ring
  exact RealMomentBound.integral_bound (μ.restrict A) _
    (((Lp.stronglyMeasurable (I.integral (Stopped s))).norm.pow (2*p)).aestronglyMeasurable.restrict)
    (fun _ => pow_nonneg (norm_nonneg _) _)
    (mul_nonneg (mul_nonneg B.2 (pow_nonneg hC _)) (integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _))) hbound

end SHE.PastReferenceStopped
