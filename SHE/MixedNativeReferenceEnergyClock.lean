module

public import SHE.MixedMovingEnergy
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

namespace SHE.MixedNativeReferenceEnergyClock
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

local notation "En"=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Er"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Past reference sections use the original native past clock and the
true global difference energy, with no supremum over physical time. -/
theorem mass (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)(h:ℝ≥0):
    (∫⁻v,ENNReal.ofReal (En v) ∂timeMeasure (H-h))≤ENNReal.ofReal Global:=by
  rw [timeMeasure_lintegral]
  have hsub:Ioc (0:ℝ) ((H-h:ℝ≥0):ℝ)⊆Ioc (0:ℝ) (H:ℝ):=by
    intro r hr
    refine ⟨hr.1,hr.2.trans ?_⟩
    exact_mod_cast (tsub_le_self (a:=H) (b:=h))
  calc
    _=(∫⁻r in Ioc (0:ℝ) ((H-h:ℝ≥0):ℝ),Er r):=by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,
        Set.indicator_of_mem (hsub hr)]
    _≤(∫⁻r in Ioc (0:ℝ) (H:ℝ),Er r):=
      lintegral_mono_set hsub
    _=ENNReal.ofReal Global:=MixedMovingEnergy.real_mass_eq
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG

include hIJ₀ hIJ₁ in
/-- Fractional past energy is integrated on the same completed-window
clock and retains the exact global-energy power and horizon factor. -/
theorem power_mass(hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)
    (h:ℝ≥0){χ:ℝ}(hχ:0≤χ)(hχ1:χ≤1):
    (∫⁻v,ENNReal.ofReal ((En v)^χ) ∂timeMeasure (H-h))≤
      (ENNReal.ofReal Global)^χ*(ENNReal.ofReal (H:ℝ))^(1-χ):=by
  have hm:Measurable (fun v=>ENNReal.ofReal (En v)):=
    ENNReal.measurable_ofReal.comp (MixedMovingEnergy.energy_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
  have he(v):ENNReal.ofReal ((En v)^χ)=(ENNReal.ofReal (En v))^χ:=
    (ENNReal.ofReal_rpow_of_nonneg
      (MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v) hχ).symm
  simp_rw [he]
  have hf:=FiniteMomentFractional.lintegral_fraction_mass
    (μ:=timeMeasure (H-h)) hm.aemeasurable hχ hχ1
  rw [timeMeasure_mass] at hf
  apply hf.trans
  apply mul_le_mul'
  · exact ENNReal.rpow_le_rpow (mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ hΛ hH B hBDG h) hχ
  · apply ENNReal.rpow_le_rpow _ (sub_nonneg.mpr hχ1)
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (tsub_le_self (a:=H) (b:=h))

include hIJ₀ hIJ₁ in
theorem weighted_mass (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)
    (h:ℝ≥0){χ:ℝ}(hχ:0≤χ)(hχ1:χ≤1)(L R:ℝ)(hL:0≤L)(hR:0≤R):
    (∫⁻v,ENNReal.ofReal (L*En v+R*(En v)^χ) ∂timeMeasure (H-h))≤
      ENNReal.ofReal L*ENNReal.ofReal Global+
        ENNReal.ofReal R*((ENNReal.ofReal Global)^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)):=by
  have he(v):ENNReal.ofReal (L*En v+R*(En v)^χ)=
      ENNReal.ofReal L*ENNReal.ofReal (En v)+ENNReal.ofReal R*ENNReal.ofReal ((En v)^χ):=by
    rw [ENNReal.ofReal_add (mul_nonneg hL (MixedMovingEnergy.energy_nonneg
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)) (mul_nonneg hR (Real.rpow_nonneg
        (MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v) _)),
      ENNReal.ofReal_mul hL,ENNReal.ofReal_mul hR]
  simp_rw [he]
  have hm:Measurable (fun v=>ENNReal.ofReal (En v)):=
    (MixedMovingEnergy.energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).ennreal_ofReal
  have hp:Measurable (fun v=>ENNReal.ofReal ((En v)^χ)):=
    ((MixedMovingEnergy.energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S).pow_const χ).ennreal_ofReal
  have hLm:Measurable (fun v=>ENNReal.ofReal L*ENNReal.ofReal (En v)):=measurable_const.mul hm
  rw [lintegral_add_left hLm,lintegral_const_mul _ hm,
    lintegral_const_mul _ hp]
  exact add_le_add (mul_le_mul' le_rfl (mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH B hBDG h)) (mul_le_mul' le_rfl (power_mass
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG h hχ hχ1))

end SHE.MixedNativeReferenceEnergyClock


