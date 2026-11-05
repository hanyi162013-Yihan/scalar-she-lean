module
public import SHE.MixedPastNativeHaarFields
public import SHE.RawKernelColumns
public import SHE.WeightedNoiseSupport
public import SHE.PhysicalOrderedGaps
public import SHE.NativeKernelFiber
public import SHE.MixedPastMeanTimeFields
public import SHE.MixedPastKernelSections
public import SHE.RelativeKernelTruncationZero
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false

namespace SHE.MixedPastSignedEndpointFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastSignedEndpointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastSignedEndpointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastSignedEndpointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastSignedEndpointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastSignedEndpointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastSignedEndpointMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastSignedEndpointMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastSignedEndpointMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total

open ActualMeanKernel NativeRandomKernel NormalizedKernelSplit NativeSignedHaarProcess SignedKernelTruncation
local notation "Endpoint"=>MixedPastKernelFields.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "Mean"=>MixedPastLiteralPoint.meanField
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local instance mixedPastSignedEndpointFields_spaceSigma:MeasurableSpace SignedKernelColumns.Space:=borel _
local instance mixedPastSignedEndpointFields_spaceBorel:BorelSpace SignedKernelColumns.Space:=⟨rfl⟩
local instance mixedPastSignedEndpointFields_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

/-- The literal countable signed endpoint field over original old times. -/
def raw (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    ((Fin k→ℝ)×Ω)→SignedKernelColumns.Space:=
  SignedKernelColumns.rawColumns
    (MixedPastKernelFields.timeField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q (fun _=>q)) mass ρ hmass hρ ell M hell
    (fun z=>CU (q,z.2)) (fun z=>CV (q,z.2))

theorem raw_measurable (hΛ:0≤Λ)(k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ):=by
  have hkernel:=MixedPastKernelFields.timeField_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 1 q
    (fun _=>q) measurable_const
  have hb(z:(Fin k→ℝ)×Ω):∃B:ℝ,0≤B∧∀y x,‖MixedPastKernelFields.timeField
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 1 q
      (fun _=>q) (z,(y,x))‖≤B:=by
    obtain ⟨B,hB,hh⟩:=ControlledFamilyKernelBounds.weightedSpatial_family_uniform_bound
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k hΛ q q z.1
    exact ⟨B,hB,fun y x=>hh (1,(U z.2,Dir z.2)) (Mean k 1 q z.2) y x⟩
  have hc:=((S.first_coefficient.mono (predictable_le_product 𝓕)).measurable).comp
    ((measurable_const (a:=q)).prodMk (measurable_snd:(Measurable (Prod.snd:(Fin k→ℝ)×Ω→Ω))))
  have hd:=((S.second_coefficient.mono (predictable_le_product 𝓕)).measurable).comp
    ((measurable_const (a:=q)).prodMk (measurable_snd:(Measurable (Prod.snd:(Fin k→ℝ)×Ω→Ω))))
  exact SignedKernelColumns.rawColumns_measurable hkernel hb hmass hρ hell _ _ hc hd

theorem raw_section (k:ℕ)(q:ℝ≥0){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(t:Fin k→ℝ)(ω:Ω):
    raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ (t,ω)=
      SignedKernelColumns.rawColumns (Endpoint k 1 q q t) mass ρ hmass hρ ell M hell
        (fun ω=>CU (q,ω)) (fun ω=>CV (q,ω)) ω:=by
  have he:=NativeKernelCongruence.operator_congr
    (MixedPastKernelFields.timeField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q (fun _=>q)) (Endpoint k 1 q q t) (t,ω) ω (fun _ _=>rfl)
  apply lp.ext
  funext j
  simp only [raw,SignedKernelColumns.rawColumns_apply,he]

theorem kernel_zero (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(hvq:v≤q)
    (ha:¬QuarterSpatialEvent.active Zero (b:ℝ) k q t)(ω:Ω)(y x:HeatCircle):
    Endpoint k 1 q q t (ω,(y,x))=0:=by
  have hnot:¬OrderedGapCoordinates.ordered (q:ℝ) (b:ℝ) k t:=by
    intro ho
    have hh:=(PhysicalOrderedGaps.strict_active_iff_ordered Zero (b:ℝ) (fun _=>rfl)
      (q:ℝ) (by exact_mod_cast hvq) k t 0 (fun _=>0)).mpr ho
    apply ha
    refine ⟨hh.1,?_⟩
    have ht:=terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    exact hh.2.trans_eq ht
  let L:=Base (1,(U ω,Dir ω))
  have hn:¬QuarterSpatialEvent.active L (b:ℝ) k q t:=by
    intro hh
    have ht:=terminal_separated L (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    exact hnot ((PhysicalOrderedGaps.strict_active_iff_ordered L (b:ℝ) (fun _=>rfl)
      (q:ℝ) (by exact_mod_cast hvq) k t 0 (fun _=>0)).mp ⟨hh.1,hh.2.trans_eq ht.symm⟩)
  exact weightedSpatial_zero_of_not_active L (b:ℝ) (fun _=>rfl) k Λ q q t
    (fun _:Unit=>Mean k 1 q ω) hn () y x

theorem raw_zero (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(hvq:v≤q)
    (ha:¬QuarterSpatialEvent.active Zero (b:ℝ) k q t){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(ω:Ω):
    raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ (t,ω)=0:=by
  rw [raw_section]
  have hz:=NativeRandomKernel.integralOperator_eq_zero_of_fiber (Endpoint k 1 q q t) ω
    (fun y x=>kernel_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q t hvq ha ω y x)
  apply lp.ext
  funext j
  simp only [SignedKernelColumns.rawColumns_apply,hz,ContinuousLinearMap.zero_apply,map_zero,lp.coeFn_zero,Pi.zero_apply]

/-- Joint current-clock, original-old-time and sample Borel structure
of the literal signed endpoint columns. -/
theorem raw_time_measurable (hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (fun z:(ℝ≥0×(Fin k→ℝ))×Ω=>
      raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        k z.1.1 hmass hρ (z.1.2,z.2)):=by
  let W:Type:=(ℝ≥0×(Fin k→ℝ))×Ω
  let Ref:=fun a:ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2
  let a:W→ℝ×Inputs:=fun z=>(1,(U z.2,Dir z.2))
  let m:W→History HeatCircle k→WordRecursion.State (1+k):=fun z=>Mean k 1 z.1.1 z.2
  let G:=familyWeightedField Ref Base a k (fun _=>Λ)
    (fun z:W=>(z.1.1:ℝ)) (fun z:W=>(z.1.1:ℝ)) m (fun z=>z.1.2)
  have hU:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have ha':Measurable a:=measurable_const.prodMk
    ((hU.comp measurable_snd).prodMk (hD.comp measurable_snd))
  have hmap:Measurable (fun z:W×History HeatCircle k=>(((1:ℝ),(z.1.1.1,z.1.2)),z.2)):=
    (measurable_const.prodMk (measurable_fst.fst.fst.prodMk measurable_fst.snd)).prodMk measurable_snd
  have hmean:=MixedPastMeanTimeFields.mean_time_joint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k
  have hm:=hmean.comp hmap
  have hq:Measurable (fun z:W=>(z.1.1:ℝ)):=measurable_subtype_coe.comp measurable_fst.fst
  have hG:=ControlledFamilyMeanFields.familyWeightedField_measurable
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm a ha' k
    (fun z:W=>(z.1.1:ℝ)) (fun z:W=>(z.1.1:ℝ)) hq hq m hm (fun z=>z.1.2) measurable_fst.snd
  have hb(z:W):∃B:ℝ,0≤B∧∀y x,‖G (z,(y,x))‖≤B:=by
    obtain ⟨B,hB,hh⟩:=ControlledFamilyKernelBounds.weightedSpatial_family_uniform_bound
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k hΛ z.1.1 z.1.1 z.1.2
    exact ⟨B,hB,fun y x=>hh (a z) (m z) y x⟩
  have hc:=((S.first_coefficient.mono (predictable_le_product 𝓕)).measurable).comp
    (measurable_fst.fst.prodMk (measurable_snd:Measurable (Prod.snd:W→Ω)))
  have hd:=((S.second_coefficient.mono (predictable_le_product 𝓕)).measurable).comp
    (measurable_fst.fst.prodMk (measurable_snd:Measurable (Prod.snd:W→Ω)))
  have hh:=SignedKernelColumns.rawColumns_measurable hG hb hmass hρ hell
    (fun z:W=>CU (z.1.1,z.2)) (fun z:W=>CV (z.1.1,z.2)) hc hd
  have heq:(fun z:W=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1.1 hmass hρ (z.1.2,z.2))=
      SignedKernelColumns.rawColumns G mass ρ hmass hρ ell M hell
        (fun z:W=>CU (z.1.1,z.2)) (fun z:W=>CV (z.1.1,z.2)):=by
    funext z
    have ho:=NativeKernelCongruence.operator_congr
      (MixedPastKernelFields.timeField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k 1 z.1.1 (fun _=>z.1.1)) G (z.1.2,z.2) z
        (fun _ _=>rfl)
    apply lp.ext
    funext j
    simp only [raw,SignedKernelColumns.rawColumns_apply,ho]
  rw [heq]
  exact hh

theorem average_time_measurable (hΛ:0≤Λ)(k:ℕ)(old:Measure (Fin k→ℝ))[SFinite old]
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):
    Measurable (fun z:ℝ≥0×Ω=>∫t,raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k z.1 hmass hρ (t,z.2) ∂old):=by
  have hh:=raw_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ k hmass hρ
  have hmap:Measurable (fun z:(ℝ≥0×Ω)×(Fin k→ℝ)=>((z.1.1,z.2),z.1.2)):=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  exact ((hh.comp hmap).stronglyMeasurable.integral_prod_right' (ν:=old)).measurable

end SHE.MixedPastSignedEndpointFields
