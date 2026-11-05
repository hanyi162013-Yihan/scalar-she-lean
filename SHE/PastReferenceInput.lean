module

public import SHE.PastReferenceBracket
public import SHE.StandardTerminalPastLocality

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastReferenceBracket
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

def energyConstant (P : CanonicalCovariance.ProfileParameters) (κ θ η h : ℝ) : ℝ :=
  HaarReference.rowConstant (P.lower-κ) (P.upper-κ) *
    (2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2 *
    ProfileVolterra.powerConstant ((P.exponent-1)/2)*h^(P.exponent/2)*(θ-η)^2

theorem energyConstant_nonneg (P : CanonicalCovariance.ProfileParameters) {κ h : ℝ}
    (hκ : κ<P.lower) (hh : 0≤h) (θ η : ℝ) : 0≤energyConstant P κ θ η h := by
  have hupper : 0≤P.upper-κ := by have := P.lower_bound 0; have := P.upper_bound 0; linarith
  have hrow := HaarReference.rowConstant_nonneg (ell := P.lower-κ) hupper
  have hv := (ProfileVolterra.powerConstant_pos
    (show -1<(P.exponent-1)/2 by linarith [P.exponent_pos])).le
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hrow (sq_nonneg _)) hv)
    (Real.rpow_nonneg hh _)) (sq_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ} (hΛ : 0≤Λ) (hκ : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (H v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data)
variable (hdi : Integrable (fun ω => ‖(data ω).2‖^2) μ)
include hΛ hsmall hvb hbH hsmallTime

theorem raw_bracket_constant (ω : Ω) :
    (∫⁻ r,ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data (r,ω)‖^2) ∂timeMeasure H)≤
      ENNReal.ofReal (energyConstant P κ θ η ((b:ℝ)-(v:ℝ))*‖(data ω).2‖^2) := by
  have he := bracket_bound P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data ω
  convert he using 1
  unfold energyConstant
  congr 1
  simp only [mul_pow,sq_abs]
  ring

include hdata hdi in
/-- The literal random-past signed reference columns define a genuine
predictable L2 input of the original full-horizon integral. Finite energy
is derived from E||D_v||², not supplied as a separate reference premise. -/
theorem raw_memLp :
    @MemLp _ _ 𝓕.predictable _ _ (raw P Λ κ θ η hκ v b data) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  have hs := raw_predictable 𝓕 P Λ κ θ η hκ v b data hdata
  have ha := hs.mono (predictable_le_product 𝓕)
  have hm : Measurable (fun p => ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp (ha.measurable.norm.pow_const 2)
  let C := energyConstant P κ θ η ((b:ℝ)-(v:ℝ))
  have hC : 0≤C := energyConstant_nonneg P hκ
    (sub_nonneg.mpr (by exact_mod_cast hvb.le)) θ η
  have hb : (∫⁻ p,ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data p‖^2) ∂energyMeasure μ H)≤
      ENNReal.ofReal (C*(∫ ω,‖(data ω).2‖^2 ∂μ)) := by
    change (∫⁻ p,ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data p‖^2) ∂(timeMeasure H).prod μ)≤_
    rw [lintegral_prod _ hm.aemeasurable,lintegral_lintegral_swap hm.aemeasurable]
    calc
      _ ≤ ∫⁻ ω,ENNReal.ofReal (C*‖(data ω).2‖^2) ∂μ :=
        lintegral_mono (raw_bracket_constant P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data)
      _ = _ := by
        rw [←ofReal_integral_eq_lintegral_ofReal (hdi.const_mul C)
          (Filter.Eventually.of_forall (fun ω => mul_nonneg hC (sq_nonneg _))),integral_const_mul]
  have hi : Integrable (fun p => ‖raw P Λ κ θ η hκ v b data p‖^2) (energyMeasure μ H) :=
    ⟨(ha.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mpr
        (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  have hl : MemLp (raw P Λ κ θ η hκ v b data) 2 (energyMeasure μ H) :=
    (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr hi
  change eLpNorm (raw P Λ κ θ η hκ v b data) 2
    ((energyMeasure μ H).trim (predictable_le_product 𝓕))<⊤
  rw [eLpNorm_trim (predictable_le_product 𝓕) hs]
  exact hl

def input : Process (E := RealHaarIntegrand.Columns) 𝓕 μ H :=
  (raw_memLp 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi).toLp
    (raw P Λ κ θ η hκ v b data)

theorem input_ae : input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi =ᵐ[energyMeasure μ H]
    raw P Λ κ θ η hκ v b data :=
  ae_eq_of_ae_eq_trim
    (raw_memLp 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi).coeFn_toLp

end SHE.PastReferenceBracket
