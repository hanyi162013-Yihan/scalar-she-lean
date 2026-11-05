module
public import SHE.MovingNativeSpatialTranslation
public import SHE.MovingNativeColumns
public import SHE.MixedPastNativeOldTimeEnergy
public import SHE.MixedPastSignedEndpointFields
public import SHE.NativeKernelCongruence
public import SHE.ShiftedPhysicalArrays
public import SHE.NativeRowTimeShift
public import SHE.MovingNativeSpatialKernel
public import SHE.ControlledMeanSpatialShift
public import SHE.MixedPastNativeKernelSemigroup

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.MovingNativeColumnTranslation
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativePointTranslation_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativePointTranslation_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativePointTranslation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativePointTranslation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativePointTranslation_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativePointTranslation_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
open PastItoInputs PastItoAlgebra PhysicalProfile


local instance movingNativePointTranslation_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativePointTranslation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance movingNativePointTranslation_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativePointTranslation_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "Past" v:max ω:max=>(embed (S.first v ω),embed (S.second v ω-S.first v ω))

local notation "Abs"=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "Mean"=>MovingNativeKernelFields.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

local notation "Common"=>MovingNativeColumns.common 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Endpoint"=>MovingNativeColumns.endpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "SpatialA" v:max=>MixedPastNativeKernelAverage.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "EndpointA" v:max=>MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm

theorem common_kernel (k:ℕ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):
    (SpatialA v) k (v+s) (v+s) (fun i=>t i+(v:ℝ)) (ω,(y,x))=
      Common k (((v,s),(t,ω)),(y,x)):=by
  rw [MovingNativeSpatialTranslation.common_absolute]
  rw [MovingNativeSpatialTranslation.field_translation,MovingNativeSpatialTranslation.field_translation]
  rfl

theorem endpoint_kernel (k:ℕ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)(y x:HeatCircle):
    (EndpointA v) k 1 (v+s) (v+s) (fun i=>t i+(v:ℝ)) (ω,(y,x))=
      Endpoint k (((v,s),(t,ω)),(y,x)):=by
  rw [MovingNativeSpatialTranslation.endpoint_absolute,MovingNativeSpatialTranslation.field_translation]
  rfl

local notation "AddA" v:max=>MixedPastNativeOldTimeEnergy.additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "BaseA" v:max=>MixedPastNativeOldTimeEnergy.base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "SignedA" v:max=>MixedPastSignedEndpointFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP
  v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "Add"=>MovingNativeColumns.additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "BaseCols"=>MovingNativeColumns.base 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
local notation "Signed"=>MovingNativeColumns.signed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem additive_translation (hΛ:0≤Λ)(k:ℕ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (AddA v) k (v+s) hmass hρ ((fun i=>t i+(v:ℝ)),ω)=Add hΛ k hmass hρ ((v,s),(t,ω)):=by
  have he:=NativeKernelCongruence.operator_congr
    ((SpatialA v) k (v+s) (v+s) (fun i=>t i+(v:ℝ))) (Common k) ω ((v,s),(t,ω))
    (fun y x=>common_kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v s t ω y x)
  apply lp.ext
  funext j
  simp only [MixedPastNativeOldTimeEnergy.additive,MixedPastNativeHaarFields.columns_apply,
    MovingNativeColumns.additive,NativeKernelHaarColumns.columns_apply,NativeKernelHaarColumns.column,NNReal.coe_add,he]

theorem base_translation (hΛ:0≤Λ)(k:ℕ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (BaseA v) k (v+s) hmass hρ ((fun i=>t i+(v:ℝ)),ω)=BaseCols hΛ k hmass hρ ((v,s),(t,ω)):=by
  have he:=NativeKernelCongruence.operator_congr
    ((SpatialA v) k (v+s) (v+s) (fun i=>t i+(v:ℝ))) (Common k) ω ((v,s),(t,ω))
    (fun y x=>common_kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v s t ω y x)
  apply lp.ext
  funext j
  simp only [MixedPastNativeOldTimeEnergy.base,MixedPastNativeHaarFields.columns_apply,
    MovingNativeColumns.base,NativeKernelHaarColumns.columns_apply,NativeKernelHaarColumns.column,
    MovingNativeColumns.coefficientU,NNReal.coe_add,he]

theorem signed_translation (k:ℕ)(v s:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    (SignedA v) k (v+s) hmass hρ ((fun i=>t i+(v:ℝ)),ω)=Signed k hmass hρ ((v,s),(t,ω)):=by
  rw [MixedPastSignedEndpointFields.raw_section]
  have he:=NativeKernelCongruence.operator_congr
    ((EndpointA v) k 1 (v+s) (v+s) (fun i=>t i+(v:ℝ))) (Endpoint k) ω ((v,s),(t,ω))
    (fun y x=>endpoint_kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v s t ω y x)
  apply lp.ext
  funext j
  simp only [MovingNativeColumns.signed,SignedKernelColumns.rawColumns_apply,
    MovingNativeColumns.coefficientU,MovingNativeColumns.coefficientV,NNReal.coe_add,he]

end SHE.MovingNativeColumnTranslation
