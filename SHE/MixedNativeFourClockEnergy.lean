module

public import SHE.MixedNativeCurrentClockBounds
public import SHE.MixedNativeSignedClockBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.MixedNativeFourClockEnergy
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedNativeFourClock_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeFourClock_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedNativeFourClock_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedNativeFourClock_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeFourClock_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedNativeFourClock_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeFourClock_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeFourClock_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeFourClock_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeFourClock_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedNativeFourClock_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedNativeFourClock_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local notation "Fcur"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Fneg"=>MixedNativeInputEnergyClock.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Global"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Neg"=>MixedActualEnergyBridge.negativeEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (scoreFloor:ℝ)(Cs:ℕ→ℝ)(k:ℕ)(hk:0<k)
variable (ρ χ η ε tail ζ:ℝ)(hρ:0<ρ)(hχ0:0≤χ)(hχ1:χ<1)(hm:χ<D.beta+2*ρ)
    (hα:0<ρ+η)(hαhalf:ρ+η<1/2)(hζ:0<ζ)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Cc"=>NativeCanonicalFrequency.currentCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Cp"=>NativeCanonicalFrequency.pastCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Ci"=>NativeCanonicalFrequency.initialCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
local notation "Cg"=>NativeCanonicalFrequency.goodCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "Cb"=>NativeCanonicalFrequency.badCoefficient D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ
local notation "qc"=>NativeBandFrequencyRates.currentDegree D.beta ρ χ ζ
local notation "qp"=>NativeBandFrequencyRates.pastDegree D.beta ζ
local notation "qg"=>SignedNativeBandFrequency.goodDegree D.beta ε ζ
local notation "qb"=>SignedNativeBandFrequency.badDegree D.beta tail ζ

include hIJ₀ hIJ₁ in
/-- The complete moving native cap has a frequency-decaying bound in
exactly four true original energy masses. No current supremum or
fixed-reference substitution enters this estimate. -/
theorem completed (hΛ:1≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)
    (n:ℕ)(ν:ℝ)(hν:1≤ν)(A Ccur Cpast Cgood Cbad:ℝ):
    let h:=NativeBandFrequencyRates.window D.beta ν
    let G:=fun r a s=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k r a ν (h-s)^2)
    ENNReal.ofReal (8*A^2*Ccur^2)*(ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,G ρ χ s*Fcur (v+s)^χ))+
    ENNReal.ofReal (8*A^2*Cpast^2)*(ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,ENNReal.ofReal (s^(-(1/2:ℝ)))*G ρ 0 s*Fcur v))+
    ENNReal.ofReal (4*A^2*Cgood^2)*(ENNReal.ofReal (ν^(-2*D.beta+2*ε))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,G (ρ+η) (2*(ρ+η)) s*Fneg hΛ hρ.le (v+s)))+
    ENNReal.ofReal (4*A^2*Cbad^2)*(ENNReal.ofReal (ν^(-2*D.beta-tail))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,G 0 0 s)) ≤
    ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Cc*ν^(-qc))*
      (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
    ENNReal.ofReal (8*A^2*Cpast^2)*ENNReal.ofReal (Cp*ν^(-qp))*ENNReal.ofReal Global+
    ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
    ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ):=by
  intro h G
  obtain ⟨hc,hp⟩:=MixedNativeCurrentClockBounds.completed
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
    (by linarith:0≤Λ) hH B hBDG n ν hν
  obtain ⟨hg,_,hb,_⟩:=MixedNativeSignedClockBounds.completed_initial
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ hΛ hρ.le n ν hν
  have hp':ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻v in Ioc (0:ℝ) ((H:ℝ)-h),∫⁻s in Ioc (0:ℝ) h,ENNReal.ofReal (s^(-(1/2:ℝ)))*G ρ 0 s*Fcur v)≤
      ENNReal.ofReal (Cp*ν^(-qp))*ENNReal.ofReal Global:=by
    convert hp using 1
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
  have hh:=add_le_add (add_le_add (add_le_add
    (mul_le_mul_right hc (ENNReal.ofReal (8*A^2*Ccur^2)))
    (mul_le_mul_right hp' (ENNReal.ofReal (8*A^2*Cpast^2))))
    (mul_le_mul_right hg (ENNReal.ofReal (4*A^2*Cgood^2))))
    (mul_le_mul_right hb (ENNReal.ofReal (4*A^2*Cbad^2)))
  simpa only [mul_assoc] using hh


include hIJ₀ hIJ₁ in
/-- The initial strip has the same true current and signed-input
masses and no artificial past-energy term. -/
theorem initial (hΛ:1≤Λ)(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDGPower 1 J B)
    (n:ℕ)(ν:ℝ)(hν:1≤ν)(A Ccur Cgood Cbad:ℝ):
    let h:=NativeBandFrequencyRates.window D.beta ν
    let G:=fun r a t q=>ENNReal.ofReal (NativeCurrentBudgetFrequency.majorant (Smooth n) scoreFloor Cs k r a ν (t-q)^2)
    ENNReal.ofReal (8*A^2*Ccur^2)*(ENNReal.ofReal (ν^(-2*D.beta))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,G ρ χ t q*Fcur q^χ))+
    ENNReal.ofReal (4*A^2*Cgood^2)*(ENNReal.ofReal (ν^(-2*D.beta+2*ε))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,G (ρ+η) (2*(ρ+η)) t q*Fneg hΛ hρ.le q))+
    ENNReal.ofReal (4*A^2*Cbad^2)*(ENNReal.ofReal (ν^(-2*D.beta-tail))*
      (∫⁻t in Ioc (0:ℝ) (min (H:ℝ) h),∫⁻q in Ioc (0:ℝ) t,G 0 0 t q)) ≤
    ENNReal.ofReal (8*A^2*Ccur^2)*ENNReal.ofReal (Ci*ν^(-qc))*
      (ENNReal.ofReal Global^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))+
    ENNReal.ofReal (4*A^2*Cgood^2)*ENNReal.ofReal (Cg*ν^(-qg))*Neg ρ+
    ENNReal.ofReal (4*A^2*Cbad^2)*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal (H:ℝ):=by
  intro h G
  have hc:=MixedNativeCurrentClockBounds.initial
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    D hT hT1 hsmall scoreFloor Cs k hk ρ χ hρ hχ0 hχ1 hm ζ hζ
    (by linarith:0≤Λ) hH B hBDG n ν hν
  obtain ⟨_,hg,_,hb⟩:=MixedNativeSignedClockBounds.completed_initial
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    D hT hT1 hsmall scoreFloor Cs k hk ρ η ε tail ζ hα hαhalf hζ hΛ hρ.le n ν hν
  have hh:=add_le_add (add_le_add
    (mul_le_mul_right hc (ENNReal.ofReal (8*A^2*Ccur^2)))
    (mul_le_mul_right hg (ENNReal.ofReal (4*A^2*Cgood^2))))
    (mul_le_mul_right hb (ENNReal.ofReal (4*A^2*Cbad^2)))
  simpa only [mul_assoc] using hh

end SHE.MixedNativeFourClockEnergy
