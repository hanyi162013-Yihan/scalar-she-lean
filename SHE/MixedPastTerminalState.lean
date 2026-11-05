module

public import SHE.MixedPastTerminalData
public import SHE.MixedPastActualMean
public import SHE.UncutNewestState
public import SHE.MixedPastJointData

public import SHE.MixedNativePastThetaMoments
public import SHE.MixedNativeEndpointLimit
public import SHE.ConditionalFatouMoment
public import SHE.MixedNativeEndpointFields
public import SHE.PastEventWeights
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalState
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastTerminalState_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastTerminalState_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastTerminalState_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastTerminalState_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastTerminalState_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastTerminalState_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


open Filter Topology AddCircle
local instance mixedPastTerminalState_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {n : ℕ}
open WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  JointPhysicalInsertion JointWordAnalytic
variable {X:Type} [MeasurableSpace X] {R:ReferenceData}

/-- Exact native terminal vector, with the newest ACTUAL V point and
all preceding stopped observations unchanged. -/
theorem mean_one_eq_terminal_state (L:Level R X n)
    (hstop:∀x i,(L.observations.observations x i).stop≤L.terminal x)
    (k:ℕ) (p:History X (k+1)) (v q:ℝ≥0)
    (hqt:(q:ℝ)=(carrier L k).nodeTime p)
    (hgap:∀i,(q:ℝ)<((carrier L k).observations.observations p.1 i).target) (ω:Ω) :
    MixedPastTerminalData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S 1 v q
      (fun i=>CoveredControlledLaw.stops L k p.1 i-(v:ℝ))
      (fun i=>CoveredControlledLaw.targets L k p.1 i-(v:ℝ))
      (CoveredControlledLaw.centers L k p.1) p.2.2 ω=
    JointWordAnalytic.state (carrier L (k+1)) Λ
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField p ω
      ((carrier L (k+1)).terminal p) := by
  have he:=UncutNewestState.terminal_append L Λ
    (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
    (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
    (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
    (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField k p ω
  apply Eq.trans (b:=appendState
    ((MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
      (ω,((carrier L k).nodeTime p,p.2.2)))
    (JointWordAnalytic.state (carrier L k) Λ
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
      p.1 ω ((carrier L k).nodeTime p))) ?_ he.symm
  have hm:=MixedPastActualMean.mean_one_eq_state
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L hstop k p.1 v q hgap ω
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change _=PredictableScalarField.wordField (Function.uncurry S.second) ω
      (((carrier L k).nodeTime p),p.2.2)
    simp only [MixedPastTerminalData.mean,WithLp.ofLp_toLp,Fin.cons_zero,one_mul,hqt]
    ring
  · simp only [MixedPastTerminalData.mean,WithLp.ofLp_toLp,Fin.cons_succ,appendState_succ]
    have hmi:=congrArg (fun z:WordRecursion.State (n+k)=>z j) hm
    simpa only [hqt] using hmi

end SHE.MixedPastTerminalState
