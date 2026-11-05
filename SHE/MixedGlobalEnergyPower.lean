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

namespace SHE.MixedGlobalEnergyPower
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedGlobalEnergyPower_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedGlobalEnergyPower_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedGlobalEnergyPower_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedGlobalEnergyPower_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedGlobalEnergyPower_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedGlobalEnergyPower_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedGlobalEnergyPower_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedGlobalEnergyPower_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedGlobalEnergyPower_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedGlobalEnergyPower_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedGlobalEnergyPower_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedGlobalEnergyPower_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)


local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- An ordinary native second moment gives a uniform cap on the TRUE
global difference energy; it is used only to compare energy powers. -/
theorem global_bound (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (B:ℝ≥0) (hBDG:StandardTerminalBDGPower 1 J B):
    Mglobal≤MixedHeatedDifferenceMoments.momentConstant 1 B κ M*(H:ℝ):=by
  let C:=MixedHeatedDifferenceMoments.momentConstant 1 B κ M
  have hC:0≤C:=MixedHeatedDifferenceMoments.momentConstant_nonneg (κ:=κ) hκ.le
    (hell.le.trans ((hbU 0).1.trans (hbU 0).2)) 1 B
  have hb:(∫⁻r in Ioc (0:ℝ) (H:ℝ),Ee r)≤ENNReal.ofReal (C*(H:ℝ)):=by
    calc
      _≤∫⁻_ in Ioc (0:ℝ) (H:ℝ),ENNReal.ofReal C:=by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hqH:r.toNNReal≤H:=by exact_mod_cast (show (r.toNNReal:ℝ)≤(H:ℝ) from by simpa only [Real.coe_toNNReal _ hr.1.le] using hr.2)
        have hh:=MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
          hΛ r.toNNReal hqH ((show (r.toNNReal:ℝ)≤(H:ℝ) from by exact_mod_cast hqH).trans hH) 1 (by decide) B hBDG
        simp only [Nat.cast_one,div_self one_ne_zero,Real.rpow_one] at hh
        simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,indicator_of_mem hr]
        exact ENNReal.ofReal_le_ofReal hh.2
      _=ENNReal.ofReal (C*(H:ℝ)):=by
        rw [lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Real.volume_Ioc,sub_zero]
        rw [ENNReal.ofReal_mul hC]
  rw [MixedMovingEnergy.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC H.2)).mp hb

include hIJ₀ hIJ₁ in
/-- A true beta energy power is controlled by the smaller chi power
with a model-derived constant, including zero global difference. -/
theorem power_bound (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (B:ℝ≥0) (hBDG:StandardTerminalBDGPower 1 J B)
    {χ β:ℝ} (hχ:0≤χ) (hχβ:χ≤β):
    Mglobal^β≤Mglobal^χ*(max 1 (MixedHeatedDifferenceMoments.momentConstant 1 B κ M*(H:ℝ)))^(β-χ):=by
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hb:=global_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B hBDG
  by_cases hz:Mglobal=0
  · rw [hz]
    by_cases hβ:β=0
    · have hc:χ=0:=by linarith
      simp only [hβ,hc,Real.rpow_zero,sub_self,mul_one]
      exact le_rfl
    · rw [Real.zero_rpow hβ]
      positivity
  · have hpos:0<Mglobal:=lt_of_le_of_ne hM (Ne.symm hz)
    calc
      Mglobal^β=Mglobal^χ*Mglobal^(β-χ):=by
        rw [←Real.rpow_add hpos]
        congr 1
        ring
      _≤Mglobal^χ*(max 1 (MixedHeatedDifferenceMoments.momentConstant 1 B κ M*(H:ℝ)))^(β-χ):=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hM (hb.trans (le_max_right 1 _)) (sub_nonneg.mpr hχβ))
          (Real.rpow_nonneg hM _)


end SHE.MixedGlobalEnergyPower
