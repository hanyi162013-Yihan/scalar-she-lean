module

public import SHE.MixedLevelOriginalAverage
public import SHE.MixedPhysicalGradientScaling
public import SHE.MixedUncutNoiseL2
public import SHE.MixedLevelGradientBounds
public import SHE.NativeWeightedTerminalCap
public import SHE.TerminalItoRawAverage
public import SHE.RootHeatGradientContinuity
public import SHE.MixedHeatNoiseL2Limit
public import SHE.RootMixedNoiseL2Limit
public import SHE.TerminalItoClosedLimit
public import SHE.TerminalItoAverageWitness
public import SHE.MixedJointIntegratedLevel
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedUncutPhysicalGradient
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω P : Type} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open Classical CutoffWordHistories CutoffCarriers
variable (k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "W"=>UncutSmoothWords.weight L k
local notation "Cut"=>(fun δ:ℝ=>fun hδ:0<δ=>MixedLevelPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (RecursiveHeatBounds.level L δ hδ 0 k))

/-- Literal full uncut physical gradient, with its integrable true heat
history weight kept outside the normalized genuine Gaussian derivative. -/
def raw(z:History P k×(ℝ≥0×Ω)):Both RealHaarInput:=W z.1 •
  MixedLevelPhysicalGradient.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S NL z
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k

theorem raw_predictable:
    @Measurable (History P k×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace (History P k)).prod 𝓕.predictable) inferInstance Raw:=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).smul
    (MixedLevelPhysicalGradient.raw_predictable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S NL)

theorem cutoff_eq (δ:ℝ)(hδ:0<δ)(z:History P k×(ℝ≥0×Ω)):
    Cut δ hδ z=if CutoffUncutComparison.Active L δ k z.1 then Raw z else 0:=by
  let a:=CutoffUncutComparison.Active L δ k z.1
  let w:ℝ:=if a then W z.1 else 0
  have ht:(RecursiveHeatBounds.level L δ hδ 0 k).test z.1=w • (NL).test z.1:=by
    rw [CutoffUncutComparison.test_eq_active L hδ k z.1]
    by_cases ha:a
    · dsimp only [a] at ha
      simp only [w,a,ha,ite_true]
      rw [UncutSmoothWords.test_eq_weight_normalized]
      rfl
    · dsimp only [a] at ha
      simp only [w,a,ha,ite_false,zero_smul]
  have hh:=MixedPhysicalGradientScaling.raw_smul
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (RecursiveHeatBounds.level L δ hδ 0 k) NL w z.1
    (CutoffCarriers.observations_eq L hδ zero_lt_one k z.1)
    (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1) ht z.2
  change Cut δ hδ z=w • MixedLevelPhysicalGradient.raw
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S NL z at hh
  rw [hh]
  by_cases ha:a
  · dsimp only [a] at ha
    simp only [w,a,ha,ite_true]
    rfl
  · dsimp only [a] at ha
    simp only [w,a,ha,ite_false,zero_smul]

theorem eventually_eq (z:History P k×(ℝ≥0×Ω)):
    ∃η:ℝ,0<η ∧ ∀δ hδ,δ<η→Cut δ hδ z=Raw z:=by
  obtain ⟨η,hη,heq⟩:=CutoffUncutComparison.eventually_test_eq L k z.1
  refine ⟨η,hη,fun δ hδ hd=>?_⟩
  have hh:=MixedPhysicalGradientScaling.raw_smul
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (RecursiveHeatBounds.level L δ hδ 0 k) NL (W z.1) z.1
    (CutoffCarriers.observations_eq L hδ zero_lt_one k z.1)
    (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1)
    (by rw [heq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized];rfl) z.2
  exact hh

end SHE.MixedUncutPhysicalGradient
