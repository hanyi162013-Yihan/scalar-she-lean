module
public import SHE.InitialNativeColumnEnergy
public import SHE.JointGammaFrozenCanonical
public import SHE.JointGammaRootHilbertPair
public import SHE.FirstGammaTerminalReferenceEnergy
public import SHE.JointGammaRootScalarPair
public import SHE.JointGammaOriginalHilbert
public import SHE.NativeBesselDifferenceIdentity
public import SHE.NativeBesselFiniteIdentity
public import SHE.MixedNativePairedRootZero
public import SHE.JointGammaRootRecursion
public import SHE.ControlledScalarReference
public import SHE.JointGammaActualEndpointPair
public import SHE.JointGammaFirstPairRecursion
public import SHE.JointGammaOriginalRegrouping

public import SHE.JointGammaEndpointCurrentNative
public import SHE.FirstGammaEndpointReferenceNative
public import SHE.NativeJointCurrentEndpoint
public import SHE.JointGammaEndpointValues
public import SHE.JointGammaOriginalIto
public import SHE.JointGammaNativeInput
public import SHE.JointGammaEndpointIto
public import SHE.JointGammaNativeRaw
public import SHE.JointGammaNativeNoise
public import SHE.NativeGammaDamping
public import SHE.JointGammaNativeGradients
public import SHE.JointGammaNativeRows
public import SHE.JointGammaScalarNoise
public import SHE.NativeJointPhysicalGammaAlgebra
public import SHE.JointGammaNativeCurrentTime
public import SHE.JointGammaNativeReferenceTime
public import SHE.NativeCanonicalVarianceIdentity
public import SHE.NativeJointGammaFields
public import SHE.JointGammaCurrentTime
public import SHE.NativeJointCurrentSections
public import SHE.JointGammaCurrentIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.JointInterpolationFields
public import SHE.ScalarCovarianceTailScale
public import SHE.NativeScalarProductAlgebra
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

namespace SHE.InitialJointGammaFrozenZero
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaOriginalIto_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaOriginalIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaOriginalIto_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaOriginalIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaOriginalIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaOriginalIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P:CanonicalCovariance.ProfileParameters)(hκP:κ<P.lower)(hΛ:0≤Λ)(b:ℝ≥0)(hbH:b≤H)(hH:(H:ℝ)≤1)
variable (B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hb0:0<b)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)
variable (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 2 J Bpast)
variable (hlocal:StandardTerminalPastLocality I₁)(Bnext:ℝ≥0)(hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local notation "OldU"=>S.first 0
local notation "OldD"=>(fun ω=>S.second 0 ω-S.first 0 ω)
local notation "OldUM"=>(((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted 0).measurable)
local notation "OldDM"=>((((show IsStronglyPredictable 𝓕 S.second from S.second_predictable).stronglyAdapted 0).sub
  ((show IsStronglyPredictable 𝓕 S.first from S.first_predictable).stronglyAdapted 0)).measurable)
local notation "hbOne"=>(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
local notation "State" ξ=>NativeCanonicalReferenceField.state 𝓕 μ H b 0 P Λ κ hκ hκP OldU OldD OldUM OldDM hbH hbOne I₀ I₁ ξ

include hΛ B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 hsmallL2 Bpast hBDGpast hlocal Bnext hBDGnext in
/-- True common initial data make both same-driver frozen terminal
references identical as original RealL2 states. -/
theorem state_equal(hwindow:(b:ℝ)≤P.horizon):
    ∀ᵐω∂μ,(State 1) (b,ω)=(State 0) (b,ω):=by
  have he:=FirstGammaTerminalReferenceEnergy.state_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV)
    (hell:=hell) (hbU:=hbU) (hbV:=hbV) (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S)
    (J:=J) (P:=P) (hκP:=hκP) (hΛ:=hΛ) (v:=0) (hH:=hH) (B:=B) (hBDG:=hBDG)
    (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    b hb0 hbH (by simpa only [NNReal.coe_zero,sub_zero] using hwindow) 1 0 hnull B0 B1 hBDG0 hBDG1
    hlocal Bnext hBDGnext
  have hzero:=InitialNativeColumnEnergy.initial_energy_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  rw [hzero,mul_zero] at he
  have hz:(∫ω,‖(State 1) (b,ω)-(State 0) (b,ω)‖^2 ∂μ)=0:=
    le_antisymm he.2 (integral_nonneg (fun _=>sq_nonneg _))
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _=>sq_nonneg _) he.1).mp hz] with ω hω
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hω))

variable (a:ℝ→ℝ)(j:ℕ)
include hΛ B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 hsmallL2 Bpast hBDGpast hlocal Bnext hBDGnext in
/-- The initial frozen band difference is zero for every root on one
original sample event, at the true terminal clock. -/
theorem frozen_field_zero(hwindow:(b:ℝ)≤P.horizon):
    ∀ᵐω∂μ,∀x:HeatCircle,
      JointGammaRootHilbertPair.frozenField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P hκP 0 b hbH hH (a:=a) j (ω,x)=0:=by
  filter_upwards [state_equal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J P hκP hΛ b hbH hH
    B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 hsmallL2 Bpast hBDGpast hlocal Bnext hBDGnext hwindow] with ω hω
  intro x
  rw [JointGammaFrozenCanonical.frozenField_eq_state]
  change ScalarHeatBands.band a (j+1) (PredictableScalarField.nativeField (State 1) ((b,ω),x))-
    ScalarHeatBands.band a (j+1) (PredictableScalarField.nativeField (State 0) ((b,ω),x))=0
  simp only [PredictableScalarField.nativeField,PredictableScalarField.unitField,hω,sub_self]
variable (ha:SmoothCylinders.BoundedSmooth a)(hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)
include hΛ B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 hsmallL2 Bpast hBDGpast hlocal Bnext hBDGnext ha in
/-- The initial-strip frozen term is zero as the ACTUAL native Hilbert
object used in the finite first-pair comparison. -/
theorem frozen_zero(hwindow:(b:ℝ)≤P.horizon):
    ∀ᵐω∂μ,JointGammaRootHilbertPair.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P hκP 0 b hbH hH (a:=a) j hL hρ ω=0:=by
  let F:Ω×HeatCircle→ℂ:=fun z=>(JointGammaRootHilbertPair.frozenField
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP 0 b hbH hH (a:=a) j z:ℂ)
  have hm:Measurable F:=Complex.continuous_ofReal.measurable.comp
    (JointGammaRootHilbertPair.frozenField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ S P hκP 0 b hbH hH ha j hb0 hnull B0 B1 hBDG0 hBDG1)
  filter_upwards [frozen_field_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J P hκP hΛ b hbH hH
    B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 hsmallL2 Bpast hBDGpast hlocal Bnext hBDGnext a j hwindow] with ω hω
  have hp:MemLp (fun x:HeatCircle=>F (ω,x)) 2 AddCircle.haarAddCircle:=by
    have hz:(fun x:HeatCircle=>F (ω,x))=(0:HeatCircle→ℂ):=by
      funext x
      simp only [F,hω x,Complex.ofReal_zero,Pi.zero_apply]
    rw [hz]
    exact MemLp.zero'
  have hs:=NativeBesselFiniteIdentity.finite_sum Λ ρ hL hρ.le (∅:Finset Unit) F hm
    (fun _=>F) (fun _=>hm) ω hp (by intro i hi;simp at hi) (by
      filter_upwards with x
      simp only [F,hω x,Complex.ofReal_zero,Finset.sum_empty])
  change NativeBesselFieldAE.value Λ ρ hL hρ.le F ω=0
  simpa only [Finset.sum_empty] using hs

end SHE.InitialJointGammaFrozenZero
