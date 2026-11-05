module

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

namespace SHE.JointGammaNativeNoise
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaNativeNoise_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaNativeNoise_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaNativeNoise_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaNativeNoise_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaNativeNoise_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaNativeNoise_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaNativeNoise_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaNativeNoise_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance jointGammaNativeNoise_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaNativeNoise_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaNativeNoise_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaNativeNoise_realSecond : SecondCountableTopology RealL2:=
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

private theorem convex_block {C:Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    (a u v:C) (d:ℝ):WithLp.toLp 2 (a,(1-d) • u+d • v)=
      (1-d) • WithLp.toLp 2 (a,u)+d • WithLp.toLp 2 (a,v):=by
  apply (WithLp.equiv 2 (C×C)).injective
  change (a,(1-d) • u+d • v)=((1-d) • a+d • a,(1-d) • u+d • v)
  apply Prod.ext
  · module
  · rfl

include hH B hBDG hIJ₀ hIJ₁ ha in
/-- Exact original finite-Itô scalar noise equals the native physical
joint row, including its original target damper and frozen gradient. -/
theorem noise_native (hb0:0<b) (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1) (θ:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐp∂energyMeasure μ H,v<p.1→p.1<b→
      (Noise θ x) p=(gCur θ p x) •
        ((1-θ*Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))) • BlockU p x+
          (θ*Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))) • BlockV p x)-
        (gRef θ p x) • BlockF θ p x:=by
  have hg:=JointGammaNativeGradients.gradients 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J P hκP hΛ v b hbH hH B hBDG hIJ₀ hIJ₁ hvb hb0 hnull B0 B1 hBDG0 hBDG1
    (ScalarHeatBands.band a (j+1)) θ
  filter_upwards [hg] with x hx
  have hp:=JointGammaScalarNoise.noise_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (Zx x) J P hκP hΛ v b (fun _=>le_rfl) hbH hvb (ScalarHeatBands.band a (j+1))
    (ScalarHeatBands.band_boundedSmooth ha (j+1)) θ
  filter_upwards [hx,hp,JointGammaNativeRows.additive 𝓕 μ H κ hκ b hbH x,
    JointGammaNativeRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP b hbH x,
    JointGammaNativeRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP b hbH x,
    JointGammaNativeRows.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP v b hbH θ x]
    with p hg hp hA hU hV hF hvp hpb
  rw [hp hvp hpb]
  rcases hg hvp hpb with ⟨hgc,hgr⟩
  dsimp only [ScalarCovarianceTailScale.observation] at hgc hgr ⊢
  change _=gCur θ p x • _-gRef θ p x • _
  rw [hgc,hgr,hA hpb,hU hpb,hV hpb,hF hpb]
  rw [convex_block]
  rfl

end SHE.JointGammaNativeNoise
