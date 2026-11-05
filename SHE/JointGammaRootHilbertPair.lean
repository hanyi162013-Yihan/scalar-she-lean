module
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

namespace SHE.JointGammaRootHilbertPair
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
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


local instance jointGammaOriginalIto_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance jointGammaOriginalIto_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaRootHilbert_nativeSecond : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance jointGammaOriginalIto_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaOriginalIto_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
attribute [local irreducible] FirstGammaEndpointConstruction.value NativeJointGammaCurrent.state
attribute [local irreducible] JointGammaNativeInput.input

variable (hvb:v≤b)
local notation "hEndOne"=>(show (b:ℝ)≤(H:ℝ) by exact_mod_cast hbH).trans hH
local notation "SU"=>Function.uncurry S.first
local notation "SV"=>Function.uncurry S.second
local notation "OldU"=>S.first v
local notation "OldD"=>(fun ω=>S.second v ω-S.first v ω)
local notation "Past"=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Zx" =>(fun x:HeatCircle=>ScalarCovarianceTailScale.observation b x)
local notation "Yx" =>(fun (θ:ℝ) (x:HeatCircle)=>FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
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
local notation "CurrentU"=>MixedNativeGammaEnergy.currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
local notation "CurrentV"=>MixedNativeGammaEnergy.currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
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
local notation "Noise" θ:max x:max=>JointGammaScalarNoise.noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
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
local notation "CUM"=>MixedNativeGammaEnergy.currentFirst_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
local notation "CVM"=>MixedNativeGammaEnergy.currentSecond_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P
local notation "FM"=>NativeCanonicalGammaEnergy.frozen_predictable (𝓕:=𝓕) (hU:=S.first_predictable) (hV:=S.second_predictable)
  (v:=v) (U:=SU) (V:=SV) (P:=P) (Λ:=Λ) (κ:=κ) (hκP:=hκP) (m:=Lower) (W:=Upper)
  (hmP:=min_le_right _ _) (hWP:=le_max_right _ _)

local notation "Root"=>(fun z:WordRecursion.State 1=>ScalarHeatBands.band a (j+1) (z 0))
local notation "Test"=>(fun (θ:ℝ)(x:HeatCircle)=>JointGammaTestFields.value P Λ θ v b hvb (Zx x) (fun _=>le_rfl) Root)
local notation "Derivative"=>(fun (θ:ℝ)(x:HeatCircle)=>JointGammaTestFields.derivative P Λ θ v b hvb (Zx x) (fun _=>le_rfl) Root)
local notation "Rows"=>(fun (θ:ℝ)(x:HeatCircle)=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  (Zx x) P hκP hΛ v b (fun _=>le_rfl) hbH θ)
local notation "Input"=>JointGammaNativeInput.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hκP hΛ v b hbH hH ha j
  hb0 hnull B0 B1 hBDG0 hBDG1 hA hβ hβ1 hh


local notation "Band"=>ScalarHeatBands.band a (j+1)
local notation "Ret" θ:max x:max ω:max=>JointGammaOriginalRegrouping.retained (a:=a)
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J P hκP hΛ v b hbH hvb j θ x ω
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

variable (hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (hJ:StandardFiniteIto.Universal 𝓕 μ H J)
/-- Original scalar-root target bound, with its physical observation type retained. -/
theorem scalarTargetBound(c:ℝ≥0):∀(x:HeatCircle)(i:Fin 1),(c:ℝ)≤((ControlledScalarReference.observations c).observations x i).target:=by
  intro x i
  exact le_rfl
/-- Original scalar-root stop bound. -/
theorem scalarStopBound(c:ℝ≥0):∀(x:HeatCircle)(i:Fin 1),(c:ℝ)≤((ControlledScalarReference.observations c).observations x i).stop:=by
  intro x i
  exact le_rfl
local notation "Family"=>ControlledScalarReference.observations b
local notation "RootSmooth"=>(ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right (EuclideanSpace.proj (0:Fin 1))
local notation "RootFamily"=>(fun _:HeatCircle=>Root)
local notation "RootUniform"=>UniformSmooth.UniformBoundedSmooth.fixed (P:=HeatCircle) RootSmooth
local notation "RootMeasurable"=>(RootSmooth).smooth.continuous.measurable.comp
  (measurable_snd:Measurable (Prod.snd:HeatCircle×WordRecursion.State 1→WordRecursion.State 1))
local notation "JF"=>MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Family (scalarTargetBound b) (scalarStopBound b) RootFamily RootUniform RootMeasurable
local notation "OF"=>MixedOrdinaryRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable
local notation "OE"=>MixedOrdinaryRootFields.error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable

variable (hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)
local notation "CapNonneg"=>JointGammaNativeInput.cap_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
  I₀ I₁ u₀ u₀ S P hκP v b hbH hH ha j hA hβ hβ1 hh
local notation "DM"=>NativeGammaDamping.measurable 𝓕 Λ v b
local notation "D0"=>NativeGammaDamping.nonneg (Ω:=Ω) Λ v b
local notation "D1"=>NativeGammaDamping.le_one (Ω:=Ω) Λ v b hΛ
local notation "A0"=>NativePairedGammaEnergy.additive 𝓕 μ H v b hbH hEndOne hL hρ hρhalf Cap Six GM GB κ hκ
local notation "A1"=>NativeConvexGammaEnergy.residual 𝓕 μ H v b hbH hEndOne hL hρ hρhalf LowerPos Cap Six GM GB
  Damping DM D0 D1 CurrentU CurrentV (Frozen 0) (Frozen 1) CUM CVM (FM 0) (FM 1)
local notation "Output"=>fun ω=>NativeHeatObservation.embed
  (I₀.integral (NativeRealFourierProcess.realProcess 𝓕 μ H A0) ω+
   I₁.integral (NativeRealFourierProcess.realProcess 𝓕 μ H A1) ω)
local notation "TF"=>(fun z:Ω×HeatCircle=>JF 0 0 z-OF 0 0 z)

/-- The true terminal frozen-reference difference, before the Bessel map. -/
def frozenField(z:Ω×HeatCircle):ℝ:=Band ((Ref 1) ((b,z.1),z.2))-Band ((Ref 0) ((b,z.1),z.2))
local notation "FF"=>frozenField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH (a:=a) j

/-- The actual native frozen term in the first recursive pair. -/
def frozen(ω:Ω):CircleL2:=NativeBesselFieldAE.value Λ ρ hL hρ.le (fun z:Ω×HeatCircle=>(FF z:ℂ)) ω

local notation "JT"=>MixedCanonicalRootHilbertExpansion.term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Family (scalarTargetBound b) (scalarStopBound b) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "OT"=>MixedOrdinaryRootHilbertExpansion.term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "Error"=>MixedOrdinaryRootHilbertExpansion.discrepancy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le

include ha hb0 hnull B0 B1 hBDG0 hBDG1 in
theorem frozenField_measurable:Measurable FF:=by
  have hi:@Measurable ((ℝ≥0×Ω)×HeatCircle) ((ℝ≥0×Ω)×HeatCircle) _ (𝓕.predictable.prod inferInstance) id :=
    (measurable_fst.mono le_rfl (predictable_le_product 𝓕)).prodMk measurable_snd
  have hm(θ:ℝ):Measurable (Ref θ):=
    (NativeJointGammaFields.reference_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b)
      (hbH:=hbH) (hb1:=hEndOne) (U:=SU) (V:=SV) (hU:=S.first_predictable) (hV:=S.second_predictable)
      (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁)
      hb0 hnull B0 B1 hBDG0 hBDG1 θ).comp hi
  have hp:Measurable (fun z:Ω×HeatCircle=>((b,z.1),z.2)):=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  exact ((ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable.comp ((hm 1).comp hp)).sub
    ((ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable.comp ((hm 0).comp hp))

include B hBDG ha hsmall in
/-- The actual first recursive pair in native Hilbert space. The Gamma
term is the SAME original two-channel Ito output, and the ordinary
discrepancy and both depth-one leaves retain their literal signs. -/
theorem formula(hlocal:StandardTerminalPastLocality J)(hFubini:StandardItoParameterFubini J)(hvb':v<b):
    ∀ᵐω∂μ,JT 0 0 ω-OT 0 0 ω=
      frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH (a:=a) j hL hρ ω-
        Output ω+(JT 2 0 ω-Error 0 ω)+(JT 0 1 ω-OT 0 1 ω):=by
  have hReal:∀i p x,(Six i (p,x)).im=0:=by intro i p x;fin_cases i <;>rfl
  obtain ⟨Y,hY,hRep,hE,hOutput⟩:=NativeJointGammaHilbertIdentity.exists_identified_output
    𝓕 μ H v b hbH hEndOne hL hρ hρhalf LowerPos Cap CapNonneg Six GM GB hReal
    Damping DM D0 D1 κ hκ CurrentU CurrentV (Frozen 0) (Frozen 1) CUM CVM (FM 0) (FM 1)
    I₀ I₁ J hIJ₀ hIJ₁ hFubini
  have hRep':∀ᵐx∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (Input x):=by
    simpa only [JointGammaNativeInput.input] using hRep
  let GY:Ω×HeatCircle→ℂ:=fun z=>(Y (z.2,z.1):ℂ)
  have hGY:Measurable GY:=Complex.continuous_ofReal.measurable.comp (hY.comp measurable_swap)
  have hEY:(∫⁻ω,MeasurableL2FieldAE.squareMass AddCircle.haarAddCircle GY ω ∂μ)<∞:=by
    change (∫⁻ω,∫⁻x,ENNReal.ofReal (‖GY (ω,x)‖^2) ∂AddCircle.haarAddCircle ∂μ)<∞
    rw [lintegral_lintegral_swap]
    · simpa only [GY,Complex.norm_real,Real.norm_eq_abs] using hE
    · exact ((hGY.norm.pow_const 2).ennreal_ofReal).aemeasurable
  have hYid:=NativeBesselFieldAE.identified_ae Λ ρ hL hρ.le μ GY hGY hEY Output
    (hOutput.mono (fun ω hω=>hω.1))
  have hjm(i:Fin 3)(k:ℕ):Measurable (JF i k):=MixedCanonicalRootFields.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Family
      (scalarTargetBound b) (scalarStopBound b) RootFamily RootUniform RootMeasurable hsmall hΛ i k
  have hom(i:Fin 2)(k:ℕ):Measurable (OF i k):=MixedOrdinaryRootFields.field_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family
      (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hsmall hΛ i k
  have hem:Measurable (OE 0):=MixedOrdinaryRootHilbertExpansion.error_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family
      (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hsmall hL 0
  have hfm:Measurable FF:=frozenField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P hκP v b hbH hH ha j hb0 hnull B0 B1 hBDG0 hBDG1
  have htm:Measurable TF:=(hjm 0 0).sub (hom 0 0)
  have hscalar:=JointGammaRootScalarPair.formula 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J
    P hκP hΛ v b hbH hH B hBDG hIJ₀ hIJ₁ hvb ha j hb0 hnull B0 B1 hBDG0 hBDG1
    hA hβ hβ1 hh hsmall hAs hJ hlocal hvb'
  have hid:∀ᵐx∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      (TF (ω,x):ℂ)+GY (ω,x)+(OE 0 (ω,x):ℂ)+(OF 0 1 (ω,x):ℂ)=
        (FF (ω,x):ℂ)+(JF 2 0 (ω,x):ℂ)+(JF 0 1 (ω,x):ℂ):=by
    filter_upwards [hscalar,hRep'] with x hx hy
    filter_upwards [hx,hy] with ω hx hy
    have hz:=MixedNativePairedRootZero.field_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Family (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      RootFamily RootUniform RootMeasurable ω x
    simp only [MixedNativePairedRootZero.field,MixedNativeJointHistory.firstData,
      MixedNativeJointHistory.secondData,PredictableWordState.Data.physicalField,
      PredictableScalarField.wordField,Real.toNNReal_coe,ScalarRootHeatLeaf.scalarState,
      WithLp.toLp_ofLp] at hz
    change TF (ω,x)=Band (PredictableScalarField.nativeField SV ((b,ω),x))-
      Band (PredictableScalarField.nativeField SU ((b,ω),x)) at hz
    have hr:TF (ω,x)+Y (x,ω)+OE 0 (ω,x)+OF 0 1 (ω,x)=FF (ω,x)+JF 2 0 (ω,x)+JF 0 1 (ω,x):=by
      change _ = _ at hx
      change Y (x,ω)=J.integral (Input x) ω at hy
      dsimp [frozenField] at *
      linarith
    change (TF (ω,x):ℂ)+(Y (x,ω):ℂ)+(OE 0 (ω,x):ℂ)+(OF 0 1 (ω,x):ℂ)=_
    simpa only [Complex.ofReal_add] using congrArg (fun r:ℝ=>(r:ℂ)) hr
  have hidd:∀ᵐω∂μ,∀ᵐx∂AddCircle.haarAddCircle,
      (TF (ω,x):ℂ)+GY (ω,x)+(OE 0 (ω,x):ℂ)+(OF 0 1 (ω,x):ℂ)=
        (FF (ω,x):ℂ)+(JF 2 0 (ω,x):ℂ)+(JF 0 1 (ω,x):ℂ):=by
    apply (Measure.ae_ae_comm _).mpr hid
    exact measurableSet_eq_fun
      ((((Complex.continuous_ofReal.measurable.comp htm).add hGY).add
        (Complex.continuous_ofReal.measurable.comp hem)).add (Complex.continuous_ofReal.measurable.comp (hom 0 1)))
      (((Complex.continuous_ofReal.measurable.comp hfm).add
        (Complex.continuous_ofReal.measurable.comp (hjm 2 0))).add (Complex.continuous_ofReal.measurable.comp (hjm 0 1)))
  filter_upwards [hidd,hYid,MeasurableL2FieldAE.good_ae AddCircle.haarAddCircle μ GY hGY hEY] with ω hid hYid hgood
  have hjp(i:Fin 3)(k:ℕ):MemLp (fun x:HeatCircle=>(JF i k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=
    MixedCanonicalRootHilbertExpansion.field_section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P hAs 1 v b hvb Family (scalarTargetBound b) (scalarStopBound b) RootFamily RootUniform RootMeasurable hsmall hL hρ.le i k ω
  have hop(i:Fin 2)(k:ℕ):MemLp (fun x:HeatCircle=>(OF i k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=
    MixedOrdinaryRootFields.section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hsmall hΛ i k ω
  have hep:=MixedOrdinaryRootHilbertExpansion.error_section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hsmall hL 0 ω
  have htp:MemLp (fun x:HeatCircle=>(TF (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
    convert (hjp 0 0).sub (hop 0 0) using 1
    ext x
    exact Complex.ofReal_sub _ _
  have hyp:MemLp (fun x=>GY (ω,x)) 2 AddCircle.haarAddCircle:=
    (MeasurableL2FieldAE.section_memLp_iff AddCircle.haarAddCircle GY hGY ω).mpr hgood
  let SumField:Ω×HeatCircle→ℂ:=fun z=>(TF z:ℂ)+GY z+(OE 0 z:ℂ)+(OF 0 1 z:ℂ)
  have hsum:Measurable SumField:=(((Complex.continuous_ofReal.measurable.comp htm).add hGY).add
    (Complex.continuous_ofReal.measurable.comp hem)).add (Complex.continuous_ofReal.measurable.comp (hom 0 1))
  have hsump:MemLp (fun x=>SumField (ω,x)) 2 AddCircle.haarAddCircle:=((htp.add hyp).add hep).add (hop 0 1)
  have hfp:MemLp (fun x:HeatCircle=>(FF (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
    apply ((hsump.sub (hjp 2 0)).sub (hjp 0 1)).ae_eq
    filter_upwards [hid] with x hx
    simp only [Pi.sub_apply]
    dsimp [SumField]
    linear_combination hx
  let Left:Fin 4→Ω×HeatCircle→ℂ:=fun i=>if i=0 then (fun z=>(TF z:ℂ))
    else if i=1 then GY else if i=2 then (fun z=>(OE 0 z:ℂ)) else (fun z=>(OF 0 1 z:ℂ))
  let Right:Fin 3→Ω×HeatCircle→ℂ:=fun i=>if i=0 then (fun z=>(FF z:ℂ))
    else if i=1 then (fun z=>(JF 2 0 z:ℂ)) else (fun z=>(JF 0 1 z:ℂ))
  have hlm(i:Fin 4):Measurable (Left i):=by
    fin_cases i
    · exact Complex.continuous_ofReal.measurable.comp htm
    · exact hGY
    · exact Complex.continuous_ofReal.measurable.comp hem
    · exact Complex.continuous_ofReal.measurable.comp (hom 0 1)
  have hrm(i:Fin 3):Measurable (Right i):=by
    fin_cases i
    · exact Complex.continuous_ofReal.measurable.comp hfm
    · exact Complex.continuous_ofReal.measurable.comp (hjm 2 0)
    · exact Complex.continuous_ofReal.measurable.comp (hjm 0 1)
  have hlp(i:Fin 4):MemLp (fun x=>Left i (ω,x)) 2 AddCircle.haarAddCircle:=by
    fin_cases i
    · exact htp
    · exact hyp
    · exact hep
    · exact hop 0 1
  have hrp(i:Fin 3):MemLp (fun x=>Right i (ω,x)) 2 AddCircle.haarAddCircle:=by
    fin_cases i
    · exact hfp
    · exact hjp 2 0
    · exact hjp 0 1
  have hl:=NativeBesselFiniteIdentity.finite_sum Λ ρ hL hρ.le Finset.univ SumField hsum Left hlm ω hsump (fun i _=>hlp i)
    (ae_of_all _ (fun x=>by simp [Left,SumField,Fin.sum_univ_succ,Fin.succ,Fin.mk.injEq,add_assoc]))
  have hr:=NativeBesselFiniteIdentity.finite_sum Λ ρ hL hρ.le Finset.univ SumField hsum Right hrm ω hsump (fun i _=>hrp i)
    (hid.mono (fun x hx=>by simpa [Right,SumField,Fin.sum_univ_succ,Fin.succ,Fin.mk.injEq,add_assoc] using hx))
  have htt:=NativeBesselDifferenceIdentity.sub Λ ρ hL hρ.le
    (fun z:Ω×HeatCircle=>(TF z:ℂ)) (fun z=>(JF 0 0 z:ℂ)) (fun z=>(OF 0 0 z:ℂ))
    (Complex.continuous_ofReal.measurable.comp htm) (Complex.continuous_ofReal.measurable.comp (hjm 0 0))
    (Complex.continuous_ofReal.measurable.comp (hom 0 0)) ω htp (hjp 0 0) (hop 0 0)
    (ae_of_all _ (fun x=>by simp only [Complex.ofReal_sub]))
  have hall:=hl.symm.trans hr
  simp [Left,Right,Fin.sum_univ_succ,Fin.succ,Fin.mk.injEq] at hall
  simp only [Complex.ofReal_sub] at htt
  rw [hYid,htt] at hall
  change (JT 0 0 ω-OT 0 0 ω)+(Output ω+(Error 0 ω+OT 0 1 ω))=
    frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH (a:=a) j hL hρ ω+(JT 2 0 ω+JT 0 1 ω) at hall
  calc
    JT 0 0 ω-OT 0 0 ω=
        ((JT 0 0 ω-OT 0 0 ω)+(Output ω+(Error 0 ω+OT 0 1 ω)))-
          (Output ω+(Error 0 ω+OT 0 1 ω)) := (add_sub_cancel_right _ _).symm
    _=(frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP v b hbH hH (a:=a) j hL hρ ω+
        (JT 2 0 ω+JT 0 1 ω))-(Output ω+(Error 0 ω+OT 0 1 ω)):=
      congrArg (fun z:CircleL2=>z-(Output ω+(Error 0 ω+OT 0 1 ω))) hall
    _=_:=by abel
end SHE.JointGammaRootHilbertPair

