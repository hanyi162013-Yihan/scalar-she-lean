module

public import SHE.MixedNativeInputEnergyClock
public import SHE.NativeCanonicalClockCoefficients

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.MixedNativeCurrentClockBounds
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedNativeCurrentClock_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeCurrentClock_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedNativeCurrentClock_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedNativeCurrentClock_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeCurrentClock_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedNativeCurrentClock_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeCurrentClock_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeCurrentClock_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeCurrentClock_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeCurrentClock_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedNativeCurrentClock_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedNativeCurrentClock_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (scoreFloor:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
variable (ρ χ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)(η:ℝ)(hη:0<η)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Cc"=>NativeCanonicalFrequency.currentCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
local notation "Cp"=>NativeCanonicalFrequency.pastCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm η hη
local notation "Ci"=>NativeCanonicalFrequency.initialCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm η hη

include hIJ₀ hIJ₁ in
/-- The completed native windows use the literal current and past
energies of the original mild pair. The coefficients are structural,
chosen before every stochastic model and smooth companion. -/
theorem completed (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)
    (n:ℕ)(ν:ℝ)(hν:1≤ν):
    let h:=NativeBandFrequencyRates.window D.beta ν
    ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,
        ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k ρ χ ν (h-s)^2)*Ee (v+s)^χ) ≤
      ENNReal.ofReal (Cc*ν^(-NativeBandFrequencyRates.currentDegree D.beta ρ χ η))*
        (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)) ∧
    ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,
        ENNReal.ofReal (s^(-(1/2:ℝ))*NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k ρ 0 ν (h-s)^2)*Ee v) ≤
      ENNReal.ofReal (Cp*ν^(-NativeBandFrequencyRates.pastDegree D.beta η))*ENNReal.ofReal Global:=by
  have hh:=(NativeCanonicalFrequency.moving_coefficients D hT hT1 hsmall scoreFloor Cs k hk
    ρ χ hρ hχ0 hχ1 hm η hη).2.2 n ν hν (H:ℝ) Ee
      (MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
  rwa [MixedMovingEnergy.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH B hBDG] at hh

include hIJ₀ hIJ₁ in
/-- The actual initial triangle keeps the newest output and current
energy, with no zero-extension omission at the start of the window. -/
theorem initial (hΛ:0≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)
    (n:ℕ)(ν:ℝ)(hν:1≤ν):
    let h:=NativeBandFrequencyRates.window D.beta ν
    ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,
        ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k ρ χ ν (t-q)^2)*Ee q^χ) ≤
      ENNReal.ofReal (Ci*ν^(-NativeBandFrequencyRates.currentDegree D.beta ρ χ η))*
        (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)):=by
  have hh:=(NativeCanonicalFrequency.initial_coefficient D hT hT1 hsmall scoreFloor Cs k hk
    ρ χ hρ hχ0 hχ1 hm η hη).2 n ν hν (H:ℝ) Ee
      (MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S)
  rwa [MixedMovingEnergy.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH B hBDG] at hh

end SHE.MixedNativeCurrentClockBounds
