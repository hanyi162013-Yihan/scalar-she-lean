module
public import SHE.InitialJointGammaFrozenZero
public import SHE.MixedNativePairedReferenceInitial
public import SHE.JointGammaFiniteHilbertExpansion
public import SHE.JointGammaRootHilbertPair
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

namespace SHE.InitialJointGammaNoise
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
local notation "Family"=>ControlledScalarReference.observations b
local notation "RootSmooth"=>(ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right (EuclideanSpace.proj (0:Fin 1))
local notation "RootFamily"=>(fun _:HeatCircle=>Root)
local notation "RootUniform"=>UniformSmooth.UniformBoundedSmooth.fixed (P:=HeatCircle) RootSmooth
local notation "RootMeasurable"=>(RootSmooth).smooth.continuous.measurable.comp
  (measurable_snd:Measurable (Prod.snd:HeatCircle×WordRecursion.State 1→WordRecursion.State 1))
local notation "JF"=>MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Family (JointGammaRootHilbertPair.scalarTargetBound b) (JointGammaRootHilbertPair.scalarStopBound b) RootFamily RootUniform RootMeasurable
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

local notation "JT"=>MixedCanonicalRootHilbertExpansion.term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Family (JointGammaRootHilbertPair.scalarTargetBound b) (JointGammaRootHilbertPair.scalarStopBound b) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "OT"=>MixedOrdinaryRootHilbertExpansion.term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "Error"=>MixedOrdinaryRootHilbertExpansion.discrepancy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le

local notation "Leaf"=>MixedNativePairedHilbertExpansion.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "Reference"=>MixedNativePairedHilbertExpansion.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "Mark"=>MixedNativePairedHilbertExpansion.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "Higher"=>MixedNativeHigherOriginalEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Family (fun _=>rfl) (fun _=>rfl) RootFamily RootUniform RootMeasurable hL hρ.le
local notation "FrozenTerm"=>JointGammaRootHilbertPair.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P hκP v b hbH hH (a:=a) j hL hρ

variable (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0)(hBDGpast:StandardTerminalBDGPower 2 J Bpast)
variable (hlocalI:StandardTerminalPastLocality I₁)(Bnext:ℝ≥0)(hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
include B hBDG ha hsmall hsmallL2 hBDGpast hlocalI hBDGnext in
/-- At the common initial past the actual zeroth recursive noise is
minus the complete original two-channel Gamma output. This uses the
genuine ordinary-U recursion and its actual initial reference. -/
theorem higher_zero_eq_neg_original(hv0:v=0)(hActual:P.coefficient=(fun z=>κ+aV z))
    (hwindow:(b:ℝ)≤P.horizon)(hfresh:(b:ℝ)≤UniformFutureProfileScores.horizon 1)
    (hlocal:StandardTerminalPastLocality J)(hFubini:StandardItoParameterFubini J)
    (Bg B8:ℝ≥0)(hBDGg:StandardTerminalBDGPower 1 J Bg)(hBDG8:StandardTerminalBDGPower 8 J B8):
    ∀ᵐω∂μ,Higher 0 ω= -Output ω:=by
  subst v
  have hp:=JointGammaFiniteHilbertExpansion.first_pair
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J P hκP hΛ 0 b hbH hH
    B hBDG hIJ₀ hIJ₁ hvb ha j hb0 hnull B0 B1 hBDG0 hBDG1 hA hβ hβ1 hh hsmall hAs hJ
    hL hρ hρhalf hlocal hFubini hb0
  have hAP:SmoothCylinders.BoundedSmooth P.coefficient:=by rw [hActual];exact hAs
  obtain ⟨C,hC,hCb⟩:=(RootUniform).bounds 0
  have hfamily:ObservationFamilyTimeShift.family (0:ℝ) Family=Family:=by
    unfold ObservationFamilyTimeShift.family ControlledScalarReference.observations
    congr 1
    funext x i
    simp only [ObservationTimeShift.observations,add_zero]
  have href:=MixedNativePairedReferenceInitial.reference_zero
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAP b Family
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) RootFamily RootUniform RootMeasurable
    J hIJ₀ hIJ₁ hnull hJ hAs (fun _ _=>le_rfl) (fun _ _=>rfl) hL hρ.le
    hActual hlocal hH hsmall hsmallL2 (fun _ _=>le_rfl) (fun _=>rfl) hwindow 0 hfresh
    (fun n hn=>False.elim (Nat.not_lt_zero n hn)) C 1 hC zero_le_one
    (by
      intro x n hn z
      have he:n=0:=by omega
      subst n
      have hb:=hCb x z
      rw [norm_iteratedFDeriv_zero] at hb ⊢
      change ‖Band (z 0)‖≤C at hb
      simpa only [pow_zero,mul_one] using hb)
    (1/2) (by norm_num) (by norm_num) 2 (by norm_num) (by norm_num)
    Bg Bpast B8 hBDGg hBDGpast (by simpa only [Nat.zero_add,Nat.reduceMul] using hBDG8)
    hρ hρhalf 0 le_rfl (by norm_num) hbH hb0
  have href0:∀ᵐω∂μ,MixedNativePairedHilbertExpansion.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hnull hJ P hAs 0 b (bot_le : (0:ℝ≥0)≤b) Family (fun _=>rfl) (fun _=>rfl)
    RootFamily RootUniform RootMeasurable hL hρ.le 0 ω=0:=by
    simpa only [MixedNativePairedReferenceEnergy.reference,NNReal.coe_zero,zero_add,hfamily] using href
  have hfrozen:=InitialJointGammaFrozenZero.frozen_zero
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J P hκP hΛ b hbH hH
    B hBDG hIJ₀ hIJ₁ hb0 hnull B0 B1 hBDG0 hBDG1 hsmallL2 Bpast hBDGpast
    hlocalI Bnext hBDGnext a j ha hL hρ hwindow
  filter_upwards [hp,href0,hfrozen] with ω hp hr hf
  simpa only [hr,hf,zero_add,zero_sub] using hp
end SHE.InitialJointGammaNoise
