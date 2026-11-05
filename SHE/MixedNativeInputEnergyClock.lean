module

public import SHE.MixedNativePairInitial
public import SHE.MixedActualEnergyBridge
public import SHE.NativeSignedHaarProcess
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedNativeInputEnergyClock
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


local instance mixedNativeInputEnergyClock_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeInputEnergyClock_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩

local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second

def energy {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(q:ℝ≥0):ℝ:=
  ∫ω,NativeSignedHaarProcess.inputEnergy hΛ hρ (CU (q,ω)) (CV (q,ω)) ∂μ
local notation "En"=>energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

def realEnergy {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(r:ℝ):ℝ:=
  (Ioc (0:ℝ) (H:ℝ)).indicator (fun r=>En hΛ hρ r.toNNReal) r
local notation "Er"=>realEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

def ennEnergy {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(r:ℝ):ℝ≥0∞:=ENNReal.ofReal (Er hΛ hρ r)
local notation "Ee"=>ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

theorem energy_measurable {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ):Measurable (En hΛ hρ):=by
  have hc:Measurable CU:=(S.first_coefficient.mono (predictable_le_product 𝓕)).measurable
  have hd:Measurable CV:=(S.second_coefficient.mono (predictable_le_product 𝓕)).measurable
  have hh:=NativeSignedHaarProcess.inputEnergy_measurable hΛ hρ _ _ hc hd
  exact hh.stronglyMeasurable.integral_prod_right' (ν:=μ) |>.measurable

theorem energy_nonneg {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(q:ℝ≥0):0≤En hΛ hρ q:=
  integral_nonneg (fun _=>sq_nonneg _)

theorem realEnergy_measurable {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ):Measurable (Er hΛ hρ):=
  ((energy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ).comp measurable_real_toNNReal).indicator measurableSet_Ioc

theorem ennEnergy_measurable {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ):Measurable (Ee hΛ hρ):=
  ENNReal.measurable_ofReal.comp (realEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ)

/-- The signed moving-current clock has exactly the original native negative-input energy mass. -/
theorem real_mass_eq {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ):
    (∫⁻r in Ioc (0:ℝ) (H:ℝ),Ee hΛ hρ r)=
      MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ:=by
  have hc:Measurable CU:=(S.first_coefficient.mono (predictable_le_product 𝓕)).measurable
  have hd:Measurable CV:=(S.second_coefficient.mono (predictable_le_product 𝓕)).measurable
  have he:MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ=
      ∫⁻q,ENNReal.ofReal (En hΛ hρ q) ∂timeMeasure H:=by
    rw [MixedActualEnergyBridge.negative_bessel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ]
    apply lintegral_congr_ae
    filter_upwards [] with q
    have hi:=NativeSignedHaarProcess.inputEnergy_integrable μ hΛ hρ
      (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω))
      (hc.comp (measurable_const.prodMk measurable_id)) (hd.comp (measurable_const.prodMk measurable_id))
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))).symm
  rw [he,timeMeasure_lintegral]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp only [ennEnergy,realEnergy,Set.indicator_of_mem hr]

/-- Pointwise physical-clock identification on the actual active native interval. -/
theorem ennEnergy_coe {ρ:ℝ}(hΛ:1≤Λ)(hρ:0≤ρ)(q:ℝ≥0)(hq0:0<q)(hqH:q≤H):
    Ee hΛ hρ (q:ℝ)=ENNReal.ofReal (En hΛ hρ q):=by
  have hq:(q:ℝ)∈Ioc (0:ℝ) (H:ℝ):=⟨by exact_mod_cast hq0,by exact_mod_cast hqH⟩
  simp only [ennEnergy,realEnergy,indicator_of_mem hq,Real.toNNReal_coe]

theorem current_coe (q:ℝ≥0)(hq0:0<q)(hqH:q≤H):
    MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (q:ℝ)=
      ENNReal.ofReal (MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q):=by
  have hq:(q:ℝ)∈Ioc (0:ℝ) (H:ℝ):=⟨by exact_mod_cast hq0,by exact_mod_cast hqH⟩
  simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,indicator_of_mem hq,Real.toNNReal_coe]

theorem current_power_coe (q:ℝ≥0)(hq0:0<q)(hqH:q≤H){χ:ℝ}(hχ:0≤χ):
    (MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (q:ℝ))^χ=
      ENNReal.ofReal ((MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q)^χ):=by
  rw [current_coe 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q hq0 hqH]
  exact (ENNReal.ofReal_rpow_of_nonneg
    (MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q) hχ)


/-- The same initial data also identify the zero endpoint of the clock. -/
theorem current_coe_all (q:ℝ≥0)(hqH:q≤H):
    MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (q:ℝ)=
      ENNReal.ofReal (MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q):=by
  by_cases hq:q=0
  · subst q
    have he:(fun ω=>‖S.second 0 ω-S.first 0 ω‖^2)=ᵐ[μ] (fun _=>0):=by
      filter_upwards [MixedNativeAdditiveResidualPair.first_zero
        𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S,
        MixedNativeAdditiveResidualPair.second_zero
        𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S] with ω hU hV
      simp only [hU,hV,sub_self,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0)]
    have hi:MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S 0=0:=by
      rw [MixedMovingEnergy.energy,integral_congr_ae he,integral_zero]
    simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,NNReal.coe_zero,
      Set.indicator_of_notMem (show (0:ℝ)∉Ioc 0 (H:ℝ) by simp),hi,ENNReal.ofReal_zero]
  · exact current_coe 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q (pos_iff_ne_zero.mpr hq) hqH

end SHE.MixedNativeInputEnergyClock
