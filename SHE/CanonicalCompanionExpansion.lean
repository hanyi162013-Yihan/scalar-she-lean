module

public import SHE.MixedNativeRandomUncutExpansion
public import SHE.SmoothComparisonParameters

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option quotPrecheck false

namespace SHE.CanonicalCompanionExpansion
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open SmoothApproximation ScalarData SmoothCylinders
open scoped ENNReal NNReal
local instance canonicalCompanionExpansion_unit : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance canonicalCompanionExpansion_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance canonicalCompanionExpansion_unitSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance canonicalCompanionExpansion_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance canonicalCompanionExpansion_circleSigma : MeasurableSpace CircleL2 := borel _
local instance canonicalCompanionExpansion_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance canonicalCompanionExpansion_circleCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance canonicalCompanionExpansion_realSigma : MeasurableSpace RealL2 := borel _
local instance canonicalCompanionExpansion_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance canonicalCompanionExpansion_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance canonicalCompanionExpansion_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance canonicalCompanionExpansion_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance canonicalCompanionExpansion_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

theorem total_boundedSmooth (D : ScalarData) (j : ℕ) (κ : ℝ) {aV : ℝ→ℝ}
    (haV : aV=D.smoothCoefficient j) : BoundedSmooth (fun z=>κ+aV z) := by
  rw [haV]
  simpa only [sub_neg_eq_add,add_comm] using
    (D.smooth_boundedSmooth j).sub (BoundedSmooth.const (-κ))

theorem total_eq (D : ScalarData) (j : ℕ) {T : ℝ} (hT : 0<T) (hT1 : T≤1)
    (hsmall : GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
    {κ : ℝ} (hκ : κ=(ScalarReduction.additiveAmplitude D.lower)^2) {aV : ℝ→ℝ}
    (haV : aV=D.smoothCoefficient j) :
    (ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall j).coefficient=(fun z=>κ+aV z) := by
  rw [hκ,haV]
  rfl

variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀z,ell≤aU z ∧ aU z≤M) (hbV : ∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (D : ScalarData) (j : ℕ) {T : ℝ} (hT : 0<T) (hT1 : T≤1)
variable (hprofile : GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (hκD : κ=(ScalarReduction.additiveAmplitude D.lower)^2) (hcompanion : aV=D.smoothCoefficient j)
local notation "P" => ControlledSmoothLimit.smoothTotalParameters D hT hT1 hprofile j
local notation "hAs" => total_boundedSmooth D j κ hcompanion
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀i,(b:ℝ)≤(Z i).target) (hstop : ∀i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
attribute [local irreducible] ControlledSmoothLimit.smoothTotalParameters
  MixedNativeRandomUncutLimits.leafMass MixedNativeRandomUncutLimits.referenceMass MixedNativeRandomUncutLimits.markMass
local notation "LM" => MixedNativeRandomUncutLimits.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "RM" => MixedNativeRandomUncutLimits.referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "MM" => MixedNativeRandomUncutLimits.markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF

include hκ haU haV hell hbU hbV u₀ v₀ S θ hvb htarget hstop F hF
  hIJ₀ hIJ₁ hκD hcompanion in
/-- Exact finite recursion for the actual rough/smooth canonical pair.
Only the SECOND residual coefficient is smooth. Cutoff removal occurs
for each fixed companion index; no uniform derivative bound is assumed. -/
def finite_expected_expansion
    (hsmall : ProfileStability.memoryConstant (P).lower (P).holder (P).exponent*
      ProfileVolterra.powerConstant (((P).exponent-2)/4)*(P).horizon^((P).exponent/4)≤1/2)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hbH : b≤H) (hwindow : (b:ℝ)-(v:ℝ)≤(P).horizon)
    (ν : Measure Unit) [IsFiniteMeasure ν] {η : ℝ} (hη : 0<η)
    (hgap : ∀i,η≤(Z i).target-(b:ℝ)) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) (depth : ℕ) :=
  MixedNativeRandomUncutExpansion.finite_expected_expansion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
    hsmall J hIJ₀ hIJ₁ hnull hJ hlocal hΛ (total_eq D j hT hT1 hprofile hκD hcompanion)
    hbH hwindow ν hη hgap A hA depth

end SHE.CanonicalCompanionExpansion
