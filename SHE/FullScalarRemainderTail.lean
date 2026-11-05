module

public import SHE.FullScalarHeatBandDecay
public import SHE.HilbertDyadicRemainder
public import SHE.RemainderBandSpans
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

namespace SHE.FullScalarRemainderTail
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance fullScalarRemainderTail_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance fullScalarRemainderTail_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance fullScalarRemainderTail_instance3 : MeasurableSpace RealL2 := borel _
local instance fullScalarRemainderTail_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullScalarRemainderTail_instance5 : MeasurableSpace CircleL2 := borel _
local instance fullScalarRemainderTail_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullScalarRemainderTail_instance7 : MeasurableSpace RealHaarInput := borel _
local instance fullScalarRemainderTail_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullScalarRemainderTail_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullScalarRemainderTail_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance fullScalarRemainderTail_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance fullScalarRemainderTail_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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



local notation "Test"=>FullScalarHeatBandEnergy.test P
local notation "Amp"=>ScalarHeatBandBernstein.amplitude P.upper P.holder P.exponent

def output (k j:ℕ) (ρ:ℝ) (z:ℝ×Ω):CircleL2:=
  FullScalarHeatBandDecay.output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
    (RemainderBandSpans.span P.exponent j) k j ρ z
local notation "Out"=>output 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP

theorem output_measurable (k j:ℕ) (ρ:ℝ):Measurable (Out k j ρ):=
  FullNativeNegativeEnergy.output_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP (RemainderBandSpans.span P.exponent j)
    (Test j) (FullScalarHeatBandEnergy.test_uniform P haP j)
    (FullScalarHeatBandEnergy.test_measurable P haP j) k ρ

include hIJ₀ hIJ₁ in
/-- The ACTUAL all-outputtime negative remainder bands form a genuine
Hilbert L2 series. Every band keeps its own manuscript window h_j;
all fields live on the same original time/sample measure. The entire
dyadic tail, and every finite cutoff, has the sharp R_J^-8 energy. -/
theorem actual_tail
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hdepth:k+1=SHE.depth P.exponent) (J0:ℕ)
    (hJH:RemainderBandSpans.span P.exponent J0≤H)
    (hJP:(RemainderBandSpans.span P.exponent J0:ℝ)≤P.horizon)
    (hJS:∀l,l<k+1→(RemainderBandSpans.span P.exponent J0:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l)
    {χ:ℝ} (hχ:0<χ) (hχβ:χ<P.exponent) (hχeq:χ=P.exponent/2)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov)
    {η:ℝ} (hη:0<η) (hηβ:η≤P.exponent/4) (ρ:ℝ) (hρ:0≤ρ) (hΛ1:1≤Λ) (hb:P.exponent≤4/25):
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
    let D:=Λ^(-ρ)*C*(Amp (k+2))^2*(2:ℝ)^(2*(P.exponent/2+η))*Mglobal^χ
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    ∃limit:Lp CircleL2 2 (νv.prod μ),
      (∀ᵐz∂νv.prod μ,HasSum (fun j:ℕ=>Out (k+1) (J0+j) ρ z) (limit z)) ∧
      Integrable (fun z=>‖limit z‖^2) (νv.prod μ) ∧
      (∫z,‖limit z‖^2 ∂νv.prod μ)≤D*(256/225:ℝ)*((2:ℝ)^J0)^(-8:ℝ) ∧
      ∀L:ℕ,Integrable (fun z=>‖∑j∈Finset.range L,Out (k+1) (J0+j) ρ z‖^2) (νv.prod μ) ∧
        (∫z,‖∑j∈Finset.range L,Out (k+1) (J0+j) ρ z‖^2 ∂νv.prod μ)≤
          D*(256/225:ℝ)*((2:ℝ)^J0)^(-8:ℝ):=by
  intro Cp Cc CC Cm base cap C D νv
  have hbase:0≤base:=mul_nonneg
    (mul_nonneg (MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1 _) (sq_nonneg _)) (sq_nonneg _)
  have hC:0≤C:=by dsimp only [C];positivity
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hD:0≤D:=by dsimp only [D];positivity
  have he (j:ℕ):Integrable (fun z:ℝ×Ω=>‖Out (k+1) (J0+j) ρ z‖^2) (νv.prod μ) ∧
      (∫z:ℝ×Ω,‖Out (k+1) (J0+j) ρ z‖^2 ∂νv.prod μ)≤D*((2:ℝ)^(J0+j))^(-8:ℝ):=by
    have hj:RemainderBandSpans.span P.exponent (J0+j)≤RemainderBandSpans.span P.exponent J0:=
      RemainderBandSpans.span_antitone P.exponent_pos.le (Nat.le_add_right J0 j)
    have hjR:(RemainderBandSpans.span P.exponent (J0+j):ℝ)≤(RemainderBandSpans.span P.exponent J0:ℝ):=hj
    have hh:=FullScalarHeatBandDecay.actual_band_decay
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP
      (RemainderBandSpans.span P.exponent (J0+j)) hlocal hΛ hH
      (RemainderBandSpans.span_pos P.exponent (J0+j)) (hj.trans hJH) (hjR.trans hJP) hsmallP k
      (fun l hl=>hjR.trans (hJS l hl)) (J0+j) hχ hχβ order horder ho0 ho1
      B0 B1 Bcov hBDG hBDG1 hBDGcov hη ρ hρ hΛ1 hdepth rfl hb hχeq hηβ
    convert! hh using 1 <;> dsimp only [D,C,base,CC,Cm,Cp,Cc,cap] <;> ring_nf <;> rfl
  let F:ℕ→(ℝ×Ω)→CircleL2:=fun j=>Out (k+1) (J0+j) ρ
  have hFm(j):Measurable (F j):=output_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP (k+1) (J0+j) ρ
  have hi(j):Integrable (fun z=>‖F j z‖^2) (νv.prod μ):=(he j).1
  have hcap(j):(∫z,‖F j z‖^2 ∂νv.prod μ)≤D*((2:ℝ)^(J0+j))^(-8:ℝ):=(he j).2
  have hs:=HilbertDyadicRemainder.summation (νv.prod μ) F hFm hi J0 hD hcap
  let limit:Lp CircleL2 2 (νv.prod μ):=∑'j,HilbertBandTails.vector (νv.prod μ) F hFm hi j
  refine ⟨limit,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,?_⟩
  intro L
  exact HilbertDyadicRemainder.finite_energy (νv.prod μ) F hFm hi J0 L hD hcap

end SHE.FullScalarRemainderTail
