module

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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.JointGammaNativeInput
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaNativeInput_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaNativeInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaNativeInput_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaNativeInput_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaNativeInput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaNativeInput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaNativeInput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaNativeInput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance jointGammaNativeInput_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaNativeInput_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaNativeInput_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaNativeInput_realSecond : SecondCountableTopology RealL2:=
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
local notation "Window" =>(fun (θ:ℝ) (x:HeatCircle) (ω:Ω)=>ControlledReferenceWindows.window P Λ θ v (Zx x) b
  (by exact_mod_cast hvb) (fun _=>le_rfl) (Past ω))
local notation "Var" θ=>NativeJointGammaFields.variance (v:=v) (b:=b) (U:=SU) (V:=SV) (P:=P) (Λ:=Λ) θ
local notation "Cur" θ=>NativeJointGammaFields.current (v:=v) (b:=b) (U:=SU) (V:=SV) (Λ:=Λ) θ
local notation "Ref" θ=>NativeJointGammaFields.reference (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
  (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) θ

variable {a:ℝ→ℝ} (ha:SmoothCylinders.BoundedSmooth a) (j:ℕ)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Upper"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "LowerPos"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "CurrentU"=>MixedNativeGammaEnergy.currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "CurrentV"=>MixedNativeGammaEnergy.currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "Frozen" =>(fun θ:ℝ=>NativeCanonicalGammaEnergy.frozen (v:=v) (U:=SU) (V:=SV)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (m:=Lower) (W:=Upper)
  (hmP:=min_le_right _ _) (hWP:=le_max_right _ _) θ)
local notation "BlockU" p:max x:max=>NativePhysicalGammaKernel.block b hκ LowerPos (CurrentU p) p x
local notation "BlockV" p:max x:max=>NativePhysicalGammaKernel.block b hκ LowerPos (CurrentV p) p x
local notation "BlockF" =>(fun (θ:ℝ) p x=>NativePhysicalGammaKernel.block b hκ LowerPos (Frozen θ p) p x)
local notation "gCur" θ:max p:max x:max=>deriv (ScalarGaussianSemigroup.heat ((Var θ) (p,x)).toNNReal
  (ScalarHeatBands.band a (j+1))) ((Cur θ) (p,x))
local notation "gRef" θ:max p:max x:max=>deriv (ScalarGaussianSemigroup.heat ((Var θ) (p,x)).toNNReal
  (ScalarHeatBands.band a (j+1))) ((Ref θ) (p,x))
local notation "Noise" θ:max x:max=>JointGammaScalarNoise.noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  (Zx x) J P hκP hΛ v b (fun _=>le_rfl) hbH hvb (ScalarHeatBands.band a (j+1)) θ

local notation "Six"=>NativeJointGammaFields.fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
  (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) a j
local notation "Damping"=>NativeGammaDamping.value (Ω:=Ω) Λ v b
local notation "Raw"=>NativeJointPhysicalGammaInput.raw v b hκ LowerPos Six CurrentU CurrentV (Frozen 0) (Frozen 1) Damping

variable (hb0:0<b) (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
variable {A β:ℝ} (hA:0≤A) (hβ:0≤β) (hβ1:β≤1) (hh:∀x y,|a x-a y|≤A*|x-y|^β)
local notation "Cap"=>ScalarHeatSingleMultiplier.cap A β j
local notation "GM"=>NativeJointGammaFields.fields_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
  (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) hb0 hnull B0 B1 hBDG0 hBDG1 a ha j
local notation "GB"=>NativeJointGammaFields.fields_bound (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
  (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) ha hA hβ hβ1 hh j
local notation "CUM"=>MixedNativeGammaEnergy.currentFirst_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "CVM"=>MixedNativeGammaEnergy.currentSecond_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "FM"=>NativeCanonicalGammaEnergy.frozen_predictable (𝓕:=𝓕) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (v:=v) (U:=SU) (V:=SV) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (m:=Lower) (W:=Upper)
  (hmP:=min_le_right _ _) (hWP:=le_max_right _ _)

include S P hκP v hbH hH ha hh hA hβ hβ1 in
theorem cap_nonneg:0≤Cap:=by
  haveI:Nonempty Ω:=nonempty_of_isProbabilityMeasure μ
  exact (norm_nonneg (Six 0 ((0,Classical.arbitrary Ω),0))).trans (GB 0 (0,Classical.arbitrary Ω) 0)

local notation "CapNonneg"=>cap_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP v b hbH hH ha j hA hβ hβ1 hh
local notation "DM"=>NativeGammaDamping.measurable 𝓕 Λ v b
local notation "DB"=>(fun p=>⟨NativeGammaDamping.nonneg (Ω:=Ω) Λ v b p,NativeGammaDamping.le_one (Ω:=Ω) Λ v b hΛ p⟩)

/-- The literal native raw row in the original predictable L² input
space. This is the process used by the ORIGINAL scalar J. -/
def input (x:HeatCircle):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  NativeJointPhysicalGammaInput.process 𝓕 v b hκ LowerPos μ H hbH hEndOne Cap CapNonneg Six GM GB
    CurrentU CurrentV (Frozen 0) (Frozen 1) CUM CVM (FM 0) (FM 1) Damping DM DB x

theorem input_ae (x:HeatCircle):
    input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP hΛ v b hbH hH ha j
      hb0 hnull B0 B1 hBDG0 hBDG1 hA hβ hβ1 hh x=ᵐ[energyMeasure μ H] fun p=>Raw (p,x):=
  NativeJointPhysicalGammaInput.process_ae 𝓕 v b hκ LowerPos μ H hbH hEndOne Cap CapNonneg Six GM GB
    CurrentU CurrentV (Frozen 0) (Frozen 1) CUM CVM (FM 0) (FM 1) Damping DM DB x

include B hBDG hIJ₀ hIJ₁ hvb in
/-- Any finite-Itô inputs with their proved literal gradient-row
versions have exactly the constructed paired native input. -/
theorem original_inputs_eq:
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀Γ0 Γ1:Process (E:=Both RealHaarInput) 𝓕 μ H,
      (∀ᵐp∂energyMeasure μ H,Γ0 p=if v<p.1 ∧ p.1<b then (Noise 0 x) p else 0)→
      (∀ᵐp∂energyMeasure μ H,Γ1 p=if v<p.1 ∧ p.1<b then (Noise 1 x) p else 0)→
      Γ0-Γ1=input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP hΛ v b hbH hH ha j
        hb0 hnull B0 B1 hBDG0 hBDG1 hA hβ hβ1 hh x:=by
  have hk:=JointGammaNativeRaw.paired_raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J P hκP hΛ v b hbH hH B hBDG hIJ₀ hIJ₁ hvb ha j hb0 hnull B0 B1 hBDG0 hBDG1
  filter_upwards [hk] with x hx
  intro Γ0 Γ1 h0 h1
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [hx,h0,h1,input_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP hΛ v b hbH hH ha j
    hb0 hnull B0 B1 hBDG0 hBDG1 hA hβ hβ1 hh x,ae_eq_of_ae_eq_trim (Lp.coeFn_sub Γ0 Γ1)] with p hp h0 h1 hi hs
  rw [hs,Pi.sub_apply,h0,h1,hi]
  by_cases hw:v<p.1 ∧ p.1<b
  · simpa only [if_pos hw] using hp
  · simp only [if_neg hw,sub_self] at hp ⊢
    exact hp

end SHE.JointGammaNativeInput
