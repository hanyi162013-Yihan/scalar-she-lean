module

public import SHE.FullScalarHeatBandEnergy
public import SHE.HighFiniteRemainderWeight
public import SHE.ScalarHeatRootBands
public import SHE.FullNativeNegativeEnergy
public import SHE.ScalarNegativeOutputEnergy
public import SHE.RetainedTerminalAllFrequency
public import SHE.FrequencyTimeInflation
public import SHE.RetainedTerminalFrequencyEnergy
public import SHE.TerminalCovarianceSquared
public import SHE.MixedGlobalEnergyPower
public import SHE.RetainedMovingRemainderEnergy
public import SHE.RetainedMovingEnergySection
public import SHE.MovingTerminalSpatialFields
public import SHE.MovingPairedProductEnergy
public import SHE.PairedBudgetFrequency
public import SHE.MovingPairedRemainderEnergy
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPairedMovingSection
public import SHE.MixedPairedMovingKernel
public import SHE.MovingPairedRMSBudget
public import SHE.MixedPastTerminalPairedLinearEnergy
public import SHE.MixedPairedCurrentClock
public import SHE.MixedPastTerminalTimeFields
public import SHE.ControlledTerminalRMSMass
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FullScalarHeatBandDecay
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingTerminalAllFrequency_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingTerminalAllFrequency_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingTerminalAllFrequency_instance3 : MeasurableSpace RealL2 := borel _
local instance movingTerminalAllFrequency_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingTerminalAllFrequency_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingTerminalAllFrequency_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingTerminalAllFrequency_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingTerminalAllFrequency_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)


local notation "Test"=>FullScalarHeatBandEnergy.test P
local notation "Amp"=>ScalarHeatBandBernstein.amplitude P.upper P.holder P.exponent

def output (k j:ℕ) (ρ:ℝ) (z:ℝ×Ω):CircleL2:=
  FullNativeNegativeEnergy.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
    (Test j) (FullScalarHeatBandEnergy.test_uniform P haP j)
    (FullScalarHeatBandEnergy.test_measurable P haP j) k ρ z
local notation "Out"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h

include hIJ₀ hIJ₁ in
theorem actual_band_decay
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hh:0<h) (hhH:h≤H)
    (hspan:(h:ℝ)≤P.horizon)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    (j:ℕ) {χ:ℝ} (hχ:0<χ) (hχβ:χ<P.exponent)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov)
    {η:ℝ} (hη:0<η) (ρ:ℝ) (hρ:0≤ρ) (hΛ1:1≤Λ)
    (hdepth:k+1=SHE.depth P.exponent)
    (hscale:(h:ℝ)=((2:ℝ)^j)^(-3*P.exponent))
    (hb:P.exponent≤4/25) (hχeq:χ=P.exponent/2) (hηβ:η≤P.exponent/4) :
    let Cp:=PairedBudgetFrequency.constant P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) χ η order B0
    let Cc:=TerminalCovarianceBudget.constant P (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) η
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let base:=CC*Cm^2*(Fintype.card (OrderedHeatForests.Choices 1 (k+1)):ℝ)^2
    let cap:=max 1 (MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M*(H:ℝ))
    let C:=2*base*(Cc/2)^2*cap^(P.exponent-χ)*(H:ℝ)^(1-P.exponent)+12*Cp^2*(H:ℝ)^(1-χ)
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    Integrable (fun z:ℝ×Ω=>‖Out (k+1) j ρ z‖^2) (νv.prod μ) ∧
      (∫z:ℝ×Ω,‖Out (k+1) j ρ z‖^2 ∂νv.prod μ)≤
        Λ^(-ρ)*C*(Amp (k+2))^2*(2:ℝ)^(2*(P.exponent/2+η))*
          ((2:ℝ)^j)^(-8:ℝ)*Mglobal^χ:=by
  intro Cp Cc CC Cm base cap C νv
  have he:=FullScalarHeatBandEnergy.actual_band_negative_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h
    hlocal hΛ hH hh hhH hspan hsmallP k hsmall j hχ hχβ
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hη ρ hρ hΛ1
  have hbase:0≤base:=mul_nonneg
    (mul_nonneg (MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1 _) (sq_nonneg _)) (sq_nonneg _)
  have hC:0≤C:=by dsimp only [C];positivity
  have hR:1≤(2:ℝ)^j:=one_le_pow₀ (show (1:ℝ)≤2 by norm_num)
  have hw:FullScalarHeatBandEnergy.rootAmplitude P k j^2*
      (1+(2:ℝ)^j)^(2*(χ+η))*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/2-(χ+η)/2)≤
      (Amp (k+2))^2*(2:ℝ)^(2*(P.exponent/2+η))*((2:ℝ)^j)^(-8:ℝ):=by
    rw [FullScalarHeatBandEnergy.rootAmplitude,mul_pow,hχeq,hscale,hdepth]
    have hexp:(SHE.depth P.exponent:ℝ)*P.exponent/2-(P.exponent/2+η)/2=
        ((SHE.depth P.exponent:ℝ)*P.exponent-P.exponent/2-η)/2:=by ring
    rw [hexp]
    have hd:=HighFiniteRemainderDegree.one_add_frequency_decay hR P.exponent_pos hb hη.le hηβ
    have hm:=mul_le_mul_of_nonneg_left hd (sq_nonneg (Amp (k+2)))
    convert! hm using 1 <;> ring
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  dsimp only at he
  have htime:((k+1:ℕ):ℝ)*P.exponent/2-(χ+η)/2=
      (((k+1:ℕ):ℝ)*P.exponent-χ-η)/2:=by ring
  rw [←htime] at he
  refine ⟨he.1,he.2.trans ?_⟩
  have hm:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (mul_nonneg (Real.rpow_nonneg hΛ (-ρ)) hC)) (Real.rpow_nonneg hM χ)
  convert! hm using 1 <;> ring

end SHE.FullScalarHeatBandDecay
