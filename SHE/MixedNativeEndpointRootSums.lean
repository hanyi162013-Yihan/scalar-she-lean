module

public import SHE.ControlledFrontAverageSums
public import SHE.MixedNativeRootTransfer
public import SHE.MixedPastMeanRootIntegrability
public import SHE.MixedPastMeanCurrent

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.MixedNativeEndpointRootSums
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal BigOperators
local instance mixedNativeEndpointRootSums_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeEndpointRootSums_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeEndpointRootSums_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeEndpointRootSums_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeEndpointRootSums_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeEndpointRootSums_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (Pair : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  HistoryProductMeasure ActualMeanKernel RootSmoothSums
local instance mixedNativeEndpointRootSums_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeEndpointRootSums_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeEndpointRootSums_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeEndpointRootSums_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : ℕ→HeatCircle→WordRecursion.State 1→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
variable (hFm : ∀ j,Measurable (fun z : HeatCircle×WordRecursion.State 1=>F j z.1 z.2))

/-- Literal root-retained endpoint cutoffs of the constructed mixed pair
are finite band sums. The original old-history integral is justified
before linearity; no field-additivity or integrability premise remains. -/
theorem endpoint_sum_ae (s : Finset ℕ) (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
      P haP v b hvb Z htarget hstop (rootSum F s) (rootSum_uniform F hF s)
        (rootSum_measurable F hFm s) k θ q=ᵐ[μ.prod haarAddCircle]
      fun z=>∑ j∈s,MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
        P haP v b hvb Z htarget hstop (F j) (hF j) (hFm j) k θ q z := by
  let pu:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair
  let pd:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair
  have hu (r : ℝ≥0) : Measurable (pu r):=
    (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair r).mono (𝓕.le r) le_rfl
  have hd (r : ℝ≥0) : Measurable (pd r):=
    (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair r).mono (𝓕.le r) le_rfl
  have he:=ControlledFrontAverageSums.average_sum_ae P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
    μ (fun ω=>(pu v ω,pd v ω)) ((hu v).prodMk (hd v)) (pu q) (pd q) (hu q) (hd q) s k q θ
  convert! he using 1 <;> rfl

theorem endpoint_integrable (j k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Integrable (MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ Pair
      P haP v b hvb Z htarget hstop (F j) (hF j) (hFm j) k θ q) (μ.prod haarAddCircle) := by
  let pu:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair
  let pd:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair
  have hu (r : ℝ≥0) : Measurable (pu r):=
    (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair r).mono (𝓕.le r) le_rfl
  have hd (r : ℝ≥0) : Measurable (pd r):=
    (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ Pair r).mono (𝓕.le r) le_rfl
  have he:=ControlledFrontAverageSums.average_integrable P P.coefficient haP Λ v b hvb Z htarget hstop
    μ (fun ω=>(pu v ω,pd v ω)) ((hu v).prodMk (hd v)) (pu q) (pd q) (hu q) (hd q)
      (F j) (hF j) (hFm j) k q θ
  convert! he using 1 <;> rfl

end SHE.MixedNativeEndpointRootSums
