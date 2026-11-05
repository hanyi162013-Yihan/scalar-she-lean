module

public import SHE.MixedPastMeanFourier
public import SHE.FamilyMeanCoordinates
public import SHE.MixedPastMeanLegIdentity
public import SHE.NativeFourierAverage
public import SHE.MixedPastMeanSupport
public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget
public import SHE.MixedPastMeanFirstMoment
public import SHE.MixedPastBaselineFTCIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanAllFourier
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanAllFourier_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanAllFourier_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanAllFourier_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanAllFourier_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanAllFourier_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanAllFourier_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanAllFourier_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanAllFourier_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanAllFourier_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

local notation "Input"=>MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Leg"=>MixedPastMeanLegIdentity.leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

/-- The exact Fourier identification extends by the proved zero support
to the whole original old-time cube, including inactive histories. -/
theorem input_fourier (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (hvq : v≤q)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) (n : ℤ) :
    fourierCoeff (Input k θ q mass ρ hmass hρ t ω) n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff
        (fun x=>Complex.ofReal (∫ y : Fin k→HeatCircle,Leg k θ q (separated k (x,t,y)) ω
          ∂Measure.pi (fun _=>haarAddCircle))) n := by
  by_cases ha : active Zero (b:ℝ) k q t
  · exact MixedPastMeanFourier.input_fourier 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hΛ hages hrootStop k θ q hvq
      mass ρ hmass hρ t ha.2 ω n
  · have hz (x : HeatCircle) (y : Fin k→HeatCircle) : Leg k θ q (separated k (x,t,y)) ω=0 := by
      let p:=separated k (x,t,y)
      have ht : (carrier Zero k).terminal p=fixedTerminal (R:=Ref (0,(0,0))) (b:ℝ) k t:=
        terminal_separated Zero (b:ℝ) (fun _=>rfl) k t x y
      by_cases hqt : (q:ℝ)<(carrier Zero k).terminal p
      · have hs : ¬StrictHistory Zero k p := by
          intro hp
          apply ha
          refine ⟨?_,?_⟩
          · exact (FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl)
              k t x (0:HeatCircle) y (fun _=>0)).mp hp
          · rwa [←ht]
        exact (MixedPastMeanLegIdentity.leg_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k θ q hvq p hqt ω).trans
          (MixedPastMeanLegIdentity.value_zero_of_not_strict 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP v b hvb Z htarget hstop F hF hFm k θ q p hs ω)
      · exact MixedPastMeanLegIdentity.leg_zero_of_not_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k θ q p hqt ω
    rw [MixedPastMeanSupport.input_zero_of_not_active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q mass ρ hmass hρ t ha ω]
    simp only [hz,integral_zero,Complex.ofReal_zero]
    simp [fourierCoeff]

end SHE.MixedPastMeanAllFourier

