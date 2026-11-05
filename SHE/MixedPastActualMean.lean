module

public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
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

namespace SHE.MixedPastActualMean
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastActualMean_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastActualMean_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastActualMean_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastActualMean_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastActualMean_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastActualMean_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open PastItoInputs PastItoAlgebra PhysicalProfile

variable (θ : ℝ)

local instance mixedPastActualMean_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastActualMean_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}


/-- The true conditional native mean is the entire joint mean path,
with stop-dependent damping and original target heat ages. It is not
the scalar compensated future-mean path. -/
theorem mean_eq_jointMeanVector (v q : ℝ≥0) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hgap : ∀ i,(q:ℝ)-(v:ℝ)<target i) (ω : Ω) :
    MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω=
    ControlledJointWeightedWord.jointMeanVector (fun i=>σ i+(v:ℝ)) (fun i=>target i+(v:ℝ))
      (fun i=>NativeHeatSpan.unitCenter (center i)) q Λ (embed (S.first q ω))
      (embed (S.second q ω-S.first q ω)) θ := by
  apply PiLp.ext
  intro i
  rw [ControlledJointWeightedWord.jointMeanVector_apply]
  have hc : StoppedGaussianScore.nativeCenter (fun i=>NativeHeatSpan.unitCenter (center i)) i=center i :=
    NativeHeatSpan.scale_inverse _
  rw [hc]
  simp only [MixedPastJointData.mean,MixedNativePastThetaCentering.current,WithLp.ofLp_toLp]
  rw [functional_physical (by linarith [hgap i] : 0<target i+(v:ℝ)-(q:ℝ)),
    functional_physical (by linarith [hgap i] : 0<target i+(v:ℝ)-(q:ℝ))]

/-- The endpoint theta=1 is exactly the actual physical mixed-pair
joint observation, before every original heat target. -/
theorem mean_one_eq_evaluate (v q : ℝ≥0) (Z : Fin n→WordRecursion.Observation)
    (hgap : ∀ i,(q:ℝ)<(Z i).target) (ω : Ω) :
    MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S 1 v q
      (fun i=>(Z i).stop-(v:ℝ)) (fun i=>(Z i).target-(v:ℝ)) (fun i=>(Z i).center) ω=
      MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z ω q := by
  apply PiLp.ext
  intro i
  simp only [MixedPastJointData.mean,MixedNativePastThetaCentering.current,WithLp.ofLp_toLp,
    sub_add_cancel,one_mul,MixedNativeJointHistory.evaluate,JointWordObserve.evaluate,WordRecursion.observe,
    ite_eq_left (hgap i),MixedNativeJointHistory.firstData,MixedNativeJointHistory.secondData,
    PredictableWordState.Data.physicalState,Real.toNNReal_coe,Function.uncurry]
  rw [←functional_physical (sub_pos.mpr (hgap i)),←functional_physical (sub_pos.mpr (hgap i)),map_sub]

variable {X : Type} [MeasurableSpace X] {R : CutoffWordLevel.ReferenceData}

/-- Literal current state of an actual recursive word. The original
stops must end by its initial terminal; for the main native scalar root
this is exactly stop=target=b. Thus covered clipping changes no damping. -/
theorem mean_one_eq_state (L : CutoffWordLevel.Level R X n)
    (hstop : ∀ x i,(L.observations.observations x i).stop ≤ L.terminal x)
    (k : ℕ) (h : CutoffWordHistories.History X k) (v q : ℝ≥0)
    (hgap : ∀ i,(q:ℝ)<((CutoffCarriers.carrier L k).observations.observations h i).target) (ω : Ω) :
    MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S 1 v q
      (fun i=>CoveredControlledLaw.stops L k h i-(v:ℝ))
      (fun i=>CoveredControlledLaw.targets L k h i-(v:ℝ)) (CoveredControlledLaw.centers L k h) ω=
    JointWordAnalytic.state (CutoffCarriers.carrier L k) Λ
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState
      (MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField
      (MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField h ω q := by
  have hs : CoveredControlledLaw.stops L k h=
      fun i=>((CutoffCarriers.carrier L k).observations.observations h i).stop := by
    funext i
    exact min_eq_left (CarrierStopBounds.stop_le_initial L hstop k h i)
  rw [hs]
  exact mean_one_eq_evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q
    ((CutoffCarriers.carrier L k).observations.observations h) hgap ω

end SHE.MixedPastActualMean
