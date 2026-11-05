module

public import SHE.MixedHilbertInputMoments
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedGlobalCurrent
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

/-- Actual manuscript-sign current difference, extended by zero off the
physical time window so that genuine Lebesgue translation applies. -/
def difference (p : ℝ×Ω) : RealL2 :=
  (Ioc (0:ℝ) (H:ℝ) ×ˢ (univ : Set Ω)).indicator
    (fun p => S.first p.1.toNNReal p.2-S.second p.1.toNNReal p.2) p

theorem difference_measurable :
    Measurable (difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) := by
  have hu := (S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hv := (S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  have hm : Measurable (fun p : ℝ×Ω => (p.1.toNNReal,p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  exact ((hu.sub hv).comp hm).indicator (measurableSet_Ioc.prod MeasurableSet.univ)

local notation "D" => difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem energy_eq :
    (∫⁻ r : ℝ,∫⁻ ω,ENNReal.ofReal (‖D (r,ω)‖^2) ∂μ)=
      ∫⁻ r,∫⁻ ω,ENNReal.ofReal (‖S.second r ω-S.first r ω‖^2) ∂μ ∂timeMeasure H := by
  rw [timeMeasure_lintegral]
  have he (r : ℝ) : (∫⁻ ω,ENNReal.ofReal (‖D (r,ω)‖^2) ∂μ)=
      (Ioc (0:ℝ) (H:ℝ)).indicator
        (fun r => ∫⁻ ω,ENNReal.ofReal (‖S.second r.toNNReal ω-S.first r.toNNReal ω‖^2) ∂μ) r := by
    classical
    by_cases hr : r∈Ioc (0:ℝ) (H:ℝ)
    · rw [indicator_of_mem hr]
      apply lintegral_congr
      intro ω
      rw [difference,indicator_of_mem (show (r,ω)∈Ioc (0:ℝ) (H:ℝ) ×ˢ (univ:Set Ω) from ⟨hr,mem_univ _⟩),norm_sub_rev]
    · rw [indicator_of_notMem hr]
      have hh (ω : Ω) : D (r,ω)=0 := indicator_of_notMem (fun h => hr h.1) _
      simp only [hh,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,ENNReal.ofReal_zero,lintegral_zero]
  simp_rw [he]
  exact lintegral_indicator measurableSet_Ioc _

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Finite global current energy is derived from the actual mixed mild
solution and standard moments; no path-space L2 input is postulated. -/
theorem energy_finite (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B) :
    (∫⁻ r : ℝ,∫⁻ ω,ENNReal.ofReal (‖D (r,ω)‖^2) ∂μ)<∞ := by
  rw [energy_eq]
  have hb (r : ℝ≥0) (hr : r≤H) :
      (∫⁻ ω,ENNReal.ofReal (‖S.second r ω-S.first r ω‖^2) ∂μ)≤
        ENNReal.ofReal (MixedHeatedDifferenceMoments.momentConstant 1 B κ M) := by
    have hh := MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ r hr ((show (r:ℝ)≤(H:ℝ) by exact_mod_cast hr).trans hH)
      1 (by decide) B hBDG
    simp only [Nat.cast_one,div_self one_ne_zero,Real.rpow_one] at hh
    rw [←ofReal_integral_eq_lintegral_ofReal hh.1 (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hh.2
  calc
    _ ≤ ∫⁻ _ : ℝ≥0,ENNReal.ofReal (MixedHeatedDifferenceMoments.momentConstant 1 B κ M) ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem H] with r hr
      exact hb r hr.2
    _ < ∞ := by rw [lintegral_const,timeMeasure_mass]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end SHE.MixedGlobalCurrent
