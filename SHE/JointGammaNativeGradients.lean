module

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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.JointGammaNativeGradients
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaNativeGradients_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaNativeGradients_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaNativeGradients_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaNativeGradients_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaNativeGradients_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaNativeGradients_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaNativeGradients_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaNativeGradients_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance jointGammaNativeGradients_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaNativeGradients_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaNativeGradients_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaNativeGradients_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
attribute [local irreducible] FirstGammaEndpointConstruction.value NativeJointGammaCurrent.state

variable (hvb:v≤b)
local notation "hEndOne"=>(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
local notation "SU"=>Function.uncurry S.first
local notation "SV"=>Function.uncurry S.second
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "Past"=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Zx" =>(fun x:HeatCircle=>ScalarCovarianceTailScale.observation b x)
local notation "Yx" =>(fun (θ:ℝ) (x:HeatCircle)=>FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  (Zx x) J P hκP hΛ v b (fun _=>le_rfl) hbH θ)
local notation "W" =>(fun (θ:ℝ) (x:HeatCircle) (ω:Ω)=>ControlledReferenceWindows.window P Λ θ v (Zx x) b
  (by exact_mod_cast hvb) (fun _=>le_rfl) (Past ω))
local notation "Var" θ=>NativeJointGammaFields.variance (v:=v) (b:=b) (U:=SU) (V:=SV) (P:=P) (Λ:=Λ) θ
local notation "Cur" θ=>NativeJointGammaFields.current (v:=v) (b:=b) (U:=SU) (V:=SV) (Λ:=Λ) θ
local notation "Ref" θ=>NativeJointGammaFields.reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
  (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) θ

include hH B hBDG hIJ₀ hIJ₁ in
/-- The finite ORIGINAL-Itô Gaussian derivatives are exactly those of
the genuine native six-slot fields on the full product event. -/
theorem gradients (hb0:0<b) (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
    (a:ℝ→ℝ) (θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐp∂energyMeasure μ H,v<p.1→p.1<b→
      (deriv (ScalarGaussianSemigroup.heat (((W θ x p.2).path p.1).val 0 0).toNNReal a)
        (JointGammaAffine.current 1 Λ θ (fun _=>(b:ℝ)) ((Yx θ x) p) 0)=
       deriv (ScalarGaussianSemigroup.heat ((Var θ) (p,x)).toNNReal a) ((Cur θ) (p,x))) ∧
      (deriv (ScalarGaussianSemigroup.heat (((W θ x p.2).path p.1).val 0 0).toNNReal a)
        (FirstGammaAffine.reference 1 Λ θ (fun _=>(b:ℝ)) ((Yx θ x) p) 0)=
       deriv (ScalarGaussianSemigroup.heat ((Var θ) (p,x)).toNNReal a) ((Ref θ) (p,x))):=by
  have hc:=JointGammaNativeCurrentTime.current_eq_field_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J P hκP hΛ v b hbH hH B hBDG hIJ₀ hIJ₁ hb0 θ
  have hr:=JointGammaNativeReferenceTime.reference_eq_field_time 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J P hκP hΛ v b hbH hH B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 θ
  filter_upwards [hc,hr] with x hc hr
  filter_upwards [hc,hr] with p hc hr hvp hpb
  have hvar:((W θ x p.2).path p.1).val 0 0=(Var θ) (p,x):=by
    exact NativeCanonicalVarianceField.path_eq_field P Λ θ v b hvb OldU OldD p.1 hvp hpb.le p.2 x
  constructor
  · rw [hvar,hc hvp hpb]
    rfl
  · rw [hvar,hr hvp hpb]
    rfl

end SHE.JointGammaNativeGradients
