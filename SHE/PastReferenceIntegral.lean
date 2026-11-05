module

public import SHE.PastReferenceInput
public import SHE.PastItoAlgebra
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastReferenceBracket
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier PastItoInputs
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

theorem post_input : post 𝓕 μ H v Input=Input := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v Input,
    input_ae 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi] with p hp hi
  rw [hp]
  by_cases hv : v<p.1
  · rw [if_pos hv]
  · rw [if_neg hv,hi]
    symm
    exact indicator_of_notMem (fun h => hv h.1.1) _

theorem input_bracket :
    ∀ᵐ ω ∂μ,(∫⁻ r,ENNReal.ofReal (‖Input (r,ω)‖^2) ∂timeMeasure H)≤
      ENNReal.ofReal (Cref*‖(data ω).2‖^2) := by
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (input_ae 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi)
  filter_upwards [Measure.ae_ae_of_ae_prod he] with ω hω
  calc
    _ = ∫⁻ r,ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data (r,ω)‖^2) ∂timeMeasure H := by
      apply lintegral_congr_ae
      filter_upwards [hω] with r hr
      dsimp only [Prod.swap] at hr
      rw [hr]
    _ ≤ _ := raw_bracket_constant P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data ω

/-- Every fixed conditional even moment of the ACTUAL original Hilbert
integral of the compatible frozen reference difference. The random past
norm remains inside the past-event expectation. Gaussianity and
independence from that past norm are not used. -/
theorem moment_on_past_event {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := E) 𝓕 μ H)
    (hlocal : StandardTerminalPastLocality I) {p : ℕ} (hp : 0<p)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p I B)
    (hmoment : Integrable (fun ω => ‖(data ω).2‖^(2*p)) μ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    Integrable (fun ω => ‖I.integral Input ω‖^(2*p)) (μ.restrict A) ∧
      (∫ ω in A,‖I.integral Input ω‖^(2*p) ∂μ)≤
        (B:ℝ)*Cref^p*(∫ ω in A,‖(data ω).2‖^(2*p) ∂μ) := by
  have hC : 0≤Cref := energyConstant_nonneg P hκ
    (sub_nonneg.mpr (by exact_mod_cast hvb.le)) θ η
  have hbr := input_bracket 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi
  have hpow : (∫⁻ ω in A,(∫⁻ r,ENNReal.ofReal (‖Input (r,ω)‖^2) ∂timeMeasure H)^p ∂μ)≤
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
  have hh := StandardTerminalPastLocality.conditional_bdg I hlocal hp hBDG v A hA Input
  rw [post_input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi] at hh
  have hbound : (∫⁻ ω in A,ENNReal.ofReal (‖I.integral Input ω‖^(2*p)) ∂μ)≤
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
    (((Lp.stronglyMeasurable (I.integral Input)).norm.pow (2*p)).aestronglyMeasurable.restrict)
    (fun _ => pow_nonneg (norm_nonneg _) _)
    (mul_nonneg (mul_nonneg B.2 (pow_nonneg hC _)) (integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _))) hbound

end SHE.PastReferenceBracket
