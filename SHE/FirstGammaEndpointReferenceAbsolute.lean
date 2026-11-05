module

public import SHE.StoppedEndpointIdentification
public import SHE.FirstGammaAbsoluteReference
public import SHE.FirstGammaEndpointCoherence
public import SHE.TwoChannelPastDifference
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

namespace SHE.FirstGammaEndpointReferenceAbsolute
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

variable (hH:(H:ℝ)≤1)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def initial (ω:Ω)(i:Fin n):ℝ:=
  functional ((Z i).target-(v:ℝ)) (Z i).center (S.first v ω)+
    θ*Real.exp (-Λ*((Z i).target-(v:ℝ)))*
      functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)

include B hBDG hH hIJ₀ hIJ₁ in
/-- The actual finite frozen reference uses a single original full-target
row on every positive prefix; its past datum is not restarted. -/
theorem positive_prefix (q:ℝ≥0)(hvq:v≤q)(hqb:q<b):
    ∀ᵐω∂μ,∀i:Fin n,Ref (Y θ (q,ω)) i=
      initial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z v θ ω i+
        J.integral (StoppedItoInputs.stop 𝓕 μ H q
          (PastItoInputs.post 𝓕 μ H v (Rref (Fin.castAdd n i)))) ω:=by
  have hgap:∀i,(q:ℝ)<(Z i).target:=fun i=>
    (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb).trans_le (htarget i)
  have hb0:0<b:=(bot_le:0≤q).trans_lt hqb
  have hp:=FirstGammaEndpointPhysical.value_eq_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ q hgap hH B hBDG hb0 hqb.le q le_rfl
  have hf:=FirstGammaAbsoluteReference.reference_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v q hgap hH (hb0.trans_le hbH) B hBDG hIJ₀ hIJ₁ θ
    (hqb.le.trans hbH) hvq
  filter_upwards [hp,hf] with ω hp hf i
  rw [hp]
  have hri:=FirstGammaEndpointCoherence.replacement_stop 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ q hgap hqb.le (Fin.castAdd n i)
  have hi:=hf i
  rw [←hri,←TwoChannelPastDifference.stop_post,StoppedInputAlgebra.stop_stop,min_self] at hi
  exact hi

include B hBDG hH hIJ₀ hIJ₁ in
/-- Compatible reference identity at the TRUE zero-age terminal heat
endpoint. Scalar continuity and original stopped L2 convergence close
the endpoint, without assuming a joint spatial scalar modification. -/
theorem terminal (hvb':v<b):
    ∀ᵐω∂μ,∀i:Fin n,Ref (Y θ (b,ω)) i=
      initial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z v θ ω i+
        J.integral (StoppedItoInputs.stop 𝓕 μ H b
          (PastItoInputs.post 𝓕 μ H v (Rref (Fin.castAdd n i)))) ω:=by
  apply ae_all_iff.mpr
  intro i
  apply StoppedEndpointIdentification.identify 𝓕 μ H J
    (PastItoInputs.post 𝓕 μ H v (Rref (Fin.castAdd n i)))
    (fun t ω=>Ref (Y θ (t,ω)) i)
    (fun ω=>initial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z v θ ω i) v b hvb'
  · intro ω
    have hb0:0<b:=(bot_le:0≤v).trans_lt hvb'
    exact ((EuclideanSpace.proj i).continuous.comp ((Ref).continuous.comp
      (FirstGammaEndpointConstruction.continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0 ω))).continuousAt
  · intro q hvq hqb
    exact (positive_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH
      B hBDG θ hH hIJ₀ hIJ₁ q hvq.le hqb).mono (fun _ h=>h i)

end SHE.FirstGammaEndpointReferenceAbsolute
