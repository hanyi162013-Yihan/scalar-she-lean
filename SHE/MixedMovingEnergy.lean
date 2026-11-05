module

public import SHE.MixedGlobalCurrent
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedMovingEnergy
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedMovingEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedMovingEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedMovingEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedMovingEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedMovingEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedMovingEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedMovingEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedMovingEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedMovingEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedMovingEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)


/-- The true current difference energy, before any uniform moment cap. -/
def energy (q : ℝ≥0) : ℝ := ∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ

/-- The manuscript's global squared difference-energy mass. -/
def globalEnergy : ℝ := ∫ z : ℝ≥0×Ω,‖S.second z.1 z.2-S.first z.1 z.2‖^2 ∂energyMeasure μ H

/-- Zero extension of the actual native energy on its physical clock. -/
def realEnergy (r : ℝ) : ℝ :=
  (Ioc (0:ℝ) (H:ℝ)).indicator (fun r=>energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S r.toNNReal) r

def ennEnergy (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal
  (realEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S r)

local notation "En"=>energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Er"=>realEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Ee"=>ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem energy_measurable : Measurable En :=
  ActualInterpolatedMeanFields.current_energy_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S

theorem energy_nonneg (q : ℝ≥0) : 0≤En q := integral_nonneg (fun _=>sq_nonneg _)
theorem globalEnergy_nonneg : 0≤Mglobal := integral_nonneg (fun _=>sq_nonneg _)

theorem realEnergy_measurable : Measurable Er :=
  ((energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).comp measurable_real_toNNReal).indicator measurableSet_Ioc

theorem ennEnergy_measurable : Measurable Ee :=
  ENNReal.measurable_ofReal.comp (realEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Finiteness of the actual global energy is derived from the original
mild pair and its checked standard second moment. -/
theorem global_integrable (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B) :
    Integrable (fun z : ℝ≥0×Ω=>‖S.second z.1 z.2-S.first z.1 z.2‖^2) (energyMeasure μ H) := by
  have hu:=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hv:=(S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  have hm:=(hv.sub hu).norm.pow_const 2
  have hh:=MixedGlobalCurrent.energy_finite 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG
  rw [MixedGlobalCurrent.energy_eq] at hh
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
  change (∫⁻ z : ℝ≥0×Ω,ENNReal.ofReal (‖S.second z.1 z.2-S.first z.1 z.2‖^2) ∂(timeMeasure H).prod μ)<∞
  exact (lintegral_prod _ (ENNReal.measurable_ofReal.comp hm).aemeasurable).trans_lt hh

include hIJ₀ hIJ₁ in
/-- The real-line energy used in moving-past translation is exactly
the original native global energy, not an upper moment bound. -/
theorem real_mass_eq (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B) :
    (∫⁻ r in Ioc (0:ℝ) (H:ℝ),Ee r)=ENNReal.ofReal Mglobal := by
  have hi:=global_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG
  have hu:=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hv:=(S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  have hm:=(hv.sub hu).norm.pow_const 2
  have he : ENNReal.ofReal Mglobal=
      ∫⁻ q,ENNReal.ofReal (En q) ∂timeMeasure H := by
    rw [globalEnergy,ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))]
    change (∫⁻ z : ℝ≥0×Ω,ENNReal.ofReal (‖S.second z.1 z.2-S.first z.1 z.2‖^2) ∂(timeMeasure H).prod μ)=_
    calc
      _=(∫⁻ q,∫⁻ ω,ENNReal.ofReal (‖S.second q ω-S.first q ω‖^2) ∂μ ∂timeMeasure H):=
        lintegral_prod _ (ENNReal.measurable_ofReal.comp hm).aemeasurable
      _=_:=?_ 
    apply lintegral_congr_ae
    filter_upwards [timeMeasure_ae_mem H] with q hq
    exact (ofReal_integral_eq_lintegral_ofReal
      (MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
        hΛ q hq.2 ((show (q:ℝ)≤(H:ℝ) from by exact_mod_cast hq.2).trans hH) 1 (by decide) B hBDG).1
      (ae_of_all _ (fun _=>sq_nonneg _))).symm
  rw [he,timeMeasure_lintegral]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [ennEnergy,realEnergy,indicator_of_mem hr]

include hIJ₀ hIJ₁ in
/-- Actual current-energy powers at v+s average into the manuscript's
global energy power. All past/current correlation is preserved, and
the exact kernel mass (including any damping gain) remains untouched. -/
theorem current_window_bound (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
    (K : ℝ→ℝ≥0∞) (hK : Measurable K) (h : ℝ) {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) :
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) h,
      K s*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+s))≤
      (∫⁻ s in Ioc (0:ℝ) h,K s)*
        (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)) := by
  have hh:=MovingPastFractional.current_window K Ee hK
    (ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) hχ hχ1 (H:ℝ) h
  rwa [real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG] at hh

include hIJ₀ hIJ₁ in
theorem past_window_bound (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
    (K : ℝ→ℝ≥0∞) (hK : Measurable K) (h : ℝ) {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) :
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) h,K s*(Ee v)^χ)≤
      (∫⁻ s in Ioc (0:ℝ) h,K s)*
        (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)) := by
  have hh:=MovingPastFractional.past_window K Ee hK
    (ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) hχ hχ1 (H:ℝ) h
  rwa [real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG] at hh

end SHE.MixedMovingEnergy

