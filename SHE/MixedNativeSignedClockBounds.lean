module

public import SHE.MixedNativeInputEnergyClock
public import SHE.NativeSignedClockCoefficients

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.MixedNativeSignedClockBounds
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedNativeSignedClock_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeSignedClock_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedNativeSignedClock_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedNativeSignedClock_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeSignedClock_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedNativeSignedClock_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeSignedClock_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeSignedClock_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeSignedClock_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeSignedClock_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedNativeSignedClock_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedNativeSignedClock_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (scoreFloor:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
variable (ρ η ε tail ζ:ℝ)(hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Cg"=>NativeCanonicalFrequency.goodCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Cb"=>NativeCanonicalFrequency.badCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Ee"=>MixedNativeInputEnergyClock.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S ρ

/-- Both actual signed-current clocks integrate against the original
native negative-input energy. The bad tail costs only the physical
horizon. All constants precede every model, smoothing index and band. -/
theorem completed_initial (hΛ:1≤Λ)(hρ:0≤ρ)(n:ℕ)(ν:ℝ)(hν:1≤ν):
    let h:=NativeBandFrequencyRates.window D.beta ν
    let Kg:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k
      (ρ+η) (2*(ρ+η)) ν (h-s)^2)
    let Kb:=fun s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k 0 0 ν (h-s)^2)
    ENNReal.ofReal (ν^(-2*D.beta+2*ε))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,Kg s*Ee hΛ hρ (v+s))≤
        ENNReal.ofReal (Cg*ν^(-SignedNativeBandFrequency.goodDegree D.beta ε ζ))*Neg ∧
    ENNReal.ofReal (ν^(-2*D.beta+2*ε))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,
        ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k
          (ρ+η) (2*(ρ+η)) ν (t-q)^2)*Ee hΛ hρ q)≤
        ENNReal.ofReal (Cg*ν^(-SignedNativeBandFrequency.goodDegree D.beta ε ζ))*Neg ∧
    ENNReal.ofReal (ν^(-2*D.beta-tail))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,Kb s)≤
        ENNReal.ofReal (Cb*ν^(-SignedNativeBandFrequency.badDegree D.beta tail ζ))*ENNReal.ofReal (H:ℝ) ∧
    ENNReal.ofReal (ν^(-2*D.beta-tail))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,
        ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k 0 0 ν (t-q)^2))≤
        ENNReal.ofReal (Cb*ν^(-SignedNativeBandFrequency.badDegree D.beta tail ζ))*ENNReal.ofReal (H:ℝ):=by
  have hh:=(NativeCanonicalFrequency.signed_coefficients D hT hT1 hsmall scoreFloor Cs k hk
    ρ η ε tail ζ hα hαhalf hζ).2.2 n ν hν (H:ℝ) (Ee hΛ hρ)
      (MixedNativeInputEnergyClock.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ)
  rwa [MixedNativeInputEnergyClock.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S hΛ hρ] at hh

end SHE.MixedNativeSignedClockBounds
