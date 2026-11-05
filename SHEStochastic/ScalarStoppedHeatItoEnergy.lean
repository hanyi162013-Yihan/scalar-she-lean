module

public import SHEStochastic.ScalarStoppedHeatFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedHeatItoEnergy
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (N : ℕ) (T : ℝ≥0)
  (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)

local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁ N T
local notation "R" => ScalarStoppedHeatFourierInput.row W hg hβ hβ₁ N T
local notation "S" => ScalarStoppedHeatFourierInput.before W N T
local notation "X" a:max n:max => J.integral (v a n)

def traceEnvelope (r : ℝ) : ℝ :=
  1+2*HeatTrace.fractionalGaussianIntegral 0*(2*r)^(-(1/2 : ℝ))

private theorem ito_one (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    (∫⁻ ω,ENNReal.ofReal (((X a n) ω)^2) ∂μ) =
      ∫⁻ p,ENNReal.ofReal (‖R a n p‖^2) ∂energyMeasure μ H := by
  have ho := (Lp.memLp (X a n)).norm.integrable_sq
  have h : (fun ω => ‖(X a n) ω‖^2) = fun ω => ((X a n) ω)^2 := by
    funext ω
    rw [Real.norm_eq_abs,sq_abs]
  have hm : Measurable (fun p => ENNReal.ofReal (‖v a n p‖^2)) :=
    (((Lp.stronglyMeasurable (v a n)).mono (predictable_le_product F)).norm.pow 2).measurable.ennreal_ofReal
  have he : (∫⁻ ω,ENNReal.ofReal (((X a n) ω)^2) ∂μ) =
      (∫⁻ ω,ENNReal.ofReal (‖(X a n) ω‖^2) ∂μ) :=
    lintegral_congr (fun ω => congrArg ENNReal.ofReal (congrFun h ω).symm)
  rw [he]
  rw [←ofReal_integral_eq_lintegral_ofReal ho (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ←realLp_norm_sq,J.isometry_energy]
  rw [←lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ScalarStoppedHeatFourierInput.input_ae F μ H W hW hc hg hβ hβ₁ N T a n]
    with p hp
  rw [hp]

private theorem pair (n : ℤ) :
    (∫⁻ ω,ENNReal.ofReal (((X Complex.reCLM n) ω)^2+((X Complex.imCLM n) ω)^2) ∂μ) =
      ∫⁻ p,ENNReal.ofReal (‖R Complex.reCLM n p‖^2+‖R Complex.imCLM n p‖^2) ∂energyMeasure μ H := by
  have hX : Measurable (fun ω => ENNReal.ofReal (((X Complex.reCLM n) ω)^2)) :=
    ((Lp.stronglyMeasurable (X Complex.reCLM n)).measurable.pow_const 2).ennreal_ofReal
  have hR : Measurable (fun p => ENNReal.ofReal (‖R Complex.reCLM n p‖^2)) :=
    (((ScalarStoppedHeatFourierInput.predictable F W hW hc hg hβ hβ₁ N T Complex.reCLM n).mono
      (predictable_le_product F)).norm.pow 2).measurable.ennreal_ofReal
  simp_rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [lintegral_add_left hX,lintegral_add_left hR,ito_one F μ H W hW hc hg hβ hβ₁ N T J,
    ito_one F μ H W hW hc hg hβ hβ₁ N T J]

open Classical in
/-- Exact Itô isometry followed by the original scalar heat trace.
The bound keeps the surviving state moment inside the causal integral. -/
theorem bound :
    (∫⁻ ω,∑' n : ℤ,ENNReal.ofReal (((X Complex.reCLM n) ω)^2+((X Complex.imCLM n) ω)^2) ∂μ) ≤
      ∫⁻ p,ENNReal.ofReal (if p∈S then traceEnvelope ((T : ℝ)-(p.1 : ℝ)) *
        (4*(‖g 0‖+(C : ℝ))^2)*(1+‖W p.1 p.2‖^2) else 0) ∂energyMeasure μ H := by
  have hX (n : ℤ) : Measurable (fun ω =>
      ENNReal.ofReal (((X Complex.reCLM n) ω)^2+((X Complex.imCLM n) ω)^2)) :=
    (((Lp.stronglyMeasurable (X Complex.reCLM n)).measurable.pow_const 2).add
      ((Lp.stronglyMeasurable (X Complex.imCLM n)).measurable.pow_const 2)).ennreal_ofReal
  have hR (n : ℤ) : Measurable (fun p =>
      ENNReal.ofReal (‖R Complex.reCLM n p‖^2+‖R Complex.imCLM n p‖^2)) := by
    have h (a : ℂ →L[ℝ] ℝ) := ((ScalarStoppedHeatFourierInput.predictable F W hW hc hg hβ hβ₁ N T a n).mono
      (predictable_le_product F)).norm.pow 2
    exact ((h Complex.reCLM).add (h Complex.imCLM)).measurable.ennreal_ofReal
  rw [lintegral_tsum (fun n => (hX n).aemeasurable)]
  simp_rw [pair F μ H W hW hc hg hβ hβ₁ N T J]
  rw [←lintegral_tsum (fun n => (hR n).aemeasurable)]
  apply lintegral_mono
  intro p
  by_cases hp : p∈S
  · let s : ℝ := (T : ℝ)-(p.1 : ℝ)
    have hs : 0<s := sub_pos.mpr hp.1
    let z := HolderCoefficientIntegrability.coefficient hβ hβ₁ hg (physical W p)
    have he (n : ℤ) : ‖R Complex.reCLM n p‖^2+‖R Complex.imCLM n p‖^2 =
        Real.exp (-(2*s)*(n : ℝ)^2)*‖z‖^2 := by
      simpa only [ite_eq_left hp] using ScalarStoppedHeatFourierInput.pair_energy W hg hβ hβ₁ N T n p
    have htr := ScalarHeatFourierEnergy.trace hs
    simp_rw [he,ite_eq_left hp]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      (htr.1.mul_right _),tsum_mul_right]
    apply ENNReal.ofReal_le_ofReal
    have hz : ‖z‖^2≤4*(‖g 0‖+(C : ℝ))^2*(1+‖W p.1 p.2‖^2) := by
      have hz := HolderCoefficientEnergyGrowth.coefficient_bound ν hg hβ hβ₁ (physical W p)
      simpa only [z,physical,LinearIsometry.norm_map] using hz
    have ht0 : 0≤traceEnvelope s := by
      unfold traceEnvelope
      have hC := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ)<1/2)).le
      positivity
    exact (mul_le_mul (show _≤traceEnvelope s from htr.2) hz (sq_nonneg _) ht0).trans_eq
      (by dsimp only [s]; ring)
  · simp only [ScalarStoppedHeatFourierInput.pair_energy,ite_eq_right hp,ENNReal.ofReal_zero,tsum_zero,le_refl]

end SHEStochastic.ScalarStoppedHeatItoEnergy
