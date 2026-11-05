module

public import SHE.FiniteSpliceInitial
public import SHE.PhysicalIto
public import SHE.FirstGammaEndpointConstruction
public import SHE.FiniteItoEnergyAnalytic
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaTestFields
public import SHE.FirstGammaParameterDerivatives
public import SHE.FirstGammaDerivativeEnvelope
public import SHE.FiniteItoSmoothAnalytic
public import SHE.FiniteItoRandomCentering
public import SHE.SmoothTimeTestRestriction
public import SHE.FiniteReferenceSpliceRows
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaEndpointValues
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance firstGammaEndpointValues_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance firstGammaEndpointValues_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance firstGammaEndpointValues_inputsBorel : BorelSpace ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
local instance firstGammaEndpointValues_inputsSecondCountable : SecondCountableTopology ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
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


local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH
variable (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)

open Set ControlledProfile UniformSmooth SmoothCylinders
variable (hvb : v≤b)
variable {F : WordRecursion.State n→ℝ} (hF : BoundedSmooth F)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (θ : ℝ)
local notation "G" => FirstGammaTestFields.value P Λ θ v b hvb Z htarget F
local notation "dG" => FirstGammaTestFields.derivative P Λ θ v b hvb Z htarget F
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "R" => FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH
local notation "Rref" => FirstGammaEndpointRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
local notation "Raw" => FiniteReferenceSplice.jointRows 𝓕 μ H v R Rref
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => FirstGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)

include B hBDG in
/-- The actual current and frozen reference start at the SAME old
random value; consequently the Gaussian comparison is zero at v. -/
theorem initial_zero (hb0 : 0<b) (hb1 : (b:ℝ)≤1) :
    ∀ᵐ ω∂μ,G (Past ω) v (Y θ (v,ω))=0 := by
  have hp:=FirstGammaEndpointConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0 hb1 B hBDG v
  have he : ∀ ω,StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z₀) Rows v ω=
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z₀) Raw v ω := by
    intro ω
    apply PiLp.ext
    intro i
    simp only [StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,
      FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,StoppedInputAlgebra.stop_stop,
      min_eq_left (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)]
  filter_upwards [hp,FiniteSpliceInitial.joint_at_past 𝓕 μ H v R Rref J z₀] with ω hp hs
  have hpair : FiniteComparisonTest.left (n+n) (Y θ (v,ω))=
      FiniteComparisonTest.right (n+n) (Y θ (v,ω)):=by rw [hp,he ω];exact hs
  rw [FirstGammaTestFields.value_apply,
    FiniteSpliceInitial.affine_equal Λ θ v (fun i=>(Z i).target) (Y θ (v,ω)) hpair,sub_self]

/-- At the true terminal heat endpoint the reserve is exactly zero,
so the comparison value is the literal difference of terminal tests. -/
theorem terminal_value (ω : Ω) : G (Past ω) b (Y θ (b,ω))=
    F (L b (Y θ (b,ω)))-F (Ref (Y θ (b,ω))) := by
  rw [FirstGammaTestFields.value_apply]
  have he : GaussianItoTest.backward (W (Past ω)) F b=F:=
    PhysicalIto.backward_terminal (W (Past ω)) F
  rw [he]

end SHE.FirstGammaEndpointValues
