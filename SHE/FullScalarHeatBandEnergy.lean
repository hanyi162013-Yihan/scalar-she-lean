module

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

namespace SHE.FullScalarHeatBandEnergy
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

/-- The actual canonical coefficient root is bounded by its own profile
parameters, independently of all smooth derivative bounds. -/
theorem coefficient_abs (z:ℝ):|P.coefficient z|≤P.upper:=by
  rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
  exact P.upper_bound z

def test (j:ℕ):HeatCircle→WordRecursion.State 1→ℝ:=
  ScalarHeatRootBands.test P.coefficient (fun _=>1) j

local notation "Test"=>test P

def rootAmplitude (k j:ℕ):ℝ:=
  ScalarHeatBandBernstein.amplitude P.upper P.holder P.exponent (k+2)*
    ((2:ℝ)^j)^(-P.exponent)

include haP in
theorem test_uniform (j:ℕ):UniformBoundedSmooth (Test j):=
  ScalarHeatRootBands.test_uniform haP (coefficient_abs P) (fun _=>1)
    (W:=1) zero_le_one (fun _=>by norm_num) j

include haP in
theorem test_measurable (j:ℕ):Measurable (fun z:HeatCircle×WordRecursion.State 1=>Test j z.1 z.2):=
  ScalarHeatRootBands.test_measurable haP (coefficient_abs P) (fun _=>1) measurable_const j

include haP in
theorem test_jets (k j:ℕ) (x:HeatCircle) (l:ℕ) (hl:l≤k+2) (z:WordRecursion.State 1):
    ‖iteratedFDeriv ℝ l (Test j x) z‖≤rootAmplitude P k j*((2:ℝ)^j)^l:=by
  simpa only [test,rootAmplitude,one_mul] using ScalarHeatRootBands.test_jets haP
    (coefficient_abs P) P.holder_nonneg P.exponent_pos.le P.exponent_le_one P.holder_bound
    (fun _:HeatCircle=>1) (W:=1) zero_le_one (fun _=>by norm_num) (k+2) j x l hl z

def actual_band_negative_energy
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
    {η:ℝ} (hη:0<η) (ρ:ℝ) (hρ:0≤ρ) (hΛ1:1≤Λ) :=
  let hA:0≤rootAmplitude P k j:=mul_nonneg
    (ScalarHeatBandBernstein.amplitude_nonneg (B:=P.upper) (β:=P.exponent) P.holder_nonneg (k+2))
    (Real.rpow_nonneg (by positivity) _)
  FullNativeNegativeEnergy.actual_negative_frequency_energy (ν:=(2:ℝ)^j)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h
    (Test j) (test_uniform P haP j) (test_measurable P haP j) J hIJ₀ hIJ₁
    hlocal hΛ hH hh hhH hspan hsmallP k hsmall hA (by positivity) hχ hχβ
    (test_jets P haP k j) order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hη ρ hρ hΛ1

end SHE.FullScalarHeatBandEnergy
