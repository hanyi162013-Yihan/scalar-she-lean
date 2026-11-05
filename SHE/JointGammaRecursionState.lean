module

public import SHE.JointGammaCurrentTime
public import SHE.MixedNativeJointHistory
public import SHE.AEContinuousVersion
public import SHE.JointInterpolationFields
public import SHE.JointGammaAffine
public import SHE.FirstGammaEndpointPhysical
public import SHE.FirstGammaEndpointCoherence
public import SHE.FirstGammaCurrentIdentity
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.JointGammaRecursionState
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaCurrentTime_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaCurrentTime_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaCurrentTime_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaCurrentTime_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaCurrentTime_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaCurrentTime_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaCurrentTime_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaCurrentTime_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


local notation "Y" => FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local instance jointGammaCurrentTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaCurrentTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaCurrentTime_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
attribute [local irreducible] functional FirstGammaEndpointConstruction.value

local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
include hH B hBDG hIJ₀ hIJ₁ in
/-- The theta-one finite current is the literal old state of the joint
recursion; the equality is on the true original time/sample measure. -/
theorem one_eq_joint (hb0:0<b)(hstop:∀ i,(Z i).stop=(Z i).target):
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→
      JointGammaAffine.current n Λ 1 (fun i=>(Z i).target) (Y 1 p)=
        MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p.2 p.1:=by
  have hc:=JointGammaCurrentTime.current_eq_joint_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hH B hBDG hIJ₀ hIJ₁ hb0 1
  filter_upwards [hc] with p hc hvp hpb
  apply PiLp.ext
  intro i
  have hqT:(p.1:ℝ)<(Z i).target:=
    (show (p.1:ℝ)<(b:ℝ) by exact_mod_cast hpb).trans_le (htarget i)
  rw [hc hvp hpb i]
  simp only [MixedNativeJointHistory.evaluate,JointWordObserve.evaluate,WithLp.ofLp_toLp,
    WordRecursion.observe,if_pos hqT,MixedNativeJointHistory.firstData,MixedNativeJointHistory.secondData,
    PredictableWordState.Data.physicalState,Real.toNNReal_coe,Function.uncurry,hstop,one_mul]
  rw [←functional_physical (sub_pos.mpr hqT),←functional_physical (sub_pos.mpr hqT),map_sub]

include hH B hBDG hIJ₀ hIJ₁ in
/-- Theta zero is an ordinary first-U observation, independently of the
joint theta-zero process used elsewhere in the recursion. -/
theorem zero_eq_ordinary (hb0:0<b):
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→
      JointGammaAffine.current n Λ 0 (fun i=>(Z i).target) (Y 0 p)=
        WordRecursion.observe (fun t=>(DU).physicalState (p.2,t))
          (fun tx=>(DU).physicalField (p.2,tx)) Z p.1:=by
  have hc:=JointGammaCurrentTime.current_eq_joint_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hH B hBDG hIJ₀ hIJ₁ hb0 0
  filter_upwards [hc] with p hc hvp hpb
  apply PiLp.ext
  intro i
  have hqT:(p.1:ℝ)<(Z i).target:=
    (show (p.1:ℝ)<(b:ℝ) by exact_mod_cast hpb).trans_le (htarget i)
  rw [hc hvp hpb i]
  simp only [zero_mul,mul_zero,add_zero,WordRecursion.observe,if_pos hqT,
    MixedNativeJointHistory.firstData,PredictableWordState.Data.physicalState,Real.toNNReal_coe,Function.uncurry]
  exact functional_physical (sub_pos.mpr hqT) _ _
end SHE.JointGammaRecursionState
