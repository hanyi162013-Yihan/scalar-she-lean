module
public import SHE.MixedPastNativeHaarFields
public import SHE.NativeKernelHaarColumns
public import SHE.MixedPastMeanTimeFields
public import SHE.ControlledThetaNativePointFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedPastNativeTimeFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeTimeFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeTimeFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeTimeFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeTimeFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeTimeFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeTimeFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastNativeTimeFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeTimeFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeTimeFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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


attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.mean

local notation "Diff"=>MixedPastNativeKernel.difference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The original current law, actual random current mean, original
history and input are jointly Borel before any spatial averaging. -/
theorem difference_time_measurable (k:ℕ):
    Measurable (fun z:((ℝ≥0×Ω)×History HeatCircle k)×HeatCircle=>
      Diff k z.1.1.1 z.1.1.1 z.1.2 z.2 z.1.1.2):=by
  let W:=((ℝ≥0×Ω)×History HeatCircle k)×HeatCircle
  have hU:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hp(θ:ℝ):Measurable (fun z:W=>(θ,(U z.1.1.2,Dir z.1.1.2))):=
    measurable_const.prodMk ((hU.comp measurable_fst.fst.snd).prodMk
      (hDir.comp measurable_fst.fst.snd))
  have hq:Measurable (fun z:W=>(z.1.1.1:ℝ)):=
    measurable_subtype_coe.comp measurable_fst.fst.fst
  have hpoint(θ:ℝ):Measurable (fun z:W=>
      MixedPastNativeConsistentPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ z.1.1.1 z.1.1.1 z.1.2 z.2 z.1.1.2):=by
    have hm:Measurable (fun z:W=>MixedPastLiteralPoint.meanField
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          k θ z.1.1.1 z.1.1.2 z.1.2):=by
      have hmap:Measurable (fun z:W=>((θ,z.1.1),z.1.2)):=
        (measurable_const.prodMk measurable_fst.fst).prodMk measurable_fst.snd
      have hg:=MixedPastMeanTimeFields.mean_time_joint_measurable
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k
      convert! hg.comp hmap using 1
    have hh:=ControlledThetaNativePointFields.rowPoint_measurable P haP Λ v b hvb Z htarget hstop F hF hFm k
      (fun z:W=>(θ,(U z.1.1.2,Dir z.1.1.2))) (hp θ)
      (fun z=>z.1.2) measurable_fst.snd
      (fun z=>(z.1.1.1:ℝ)) (fun z=>(z.1.1.1:ℝ)) hq hq
      (fun z=>MixedPastLiteralPoint.meanField
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
          k θ z.1.1.1 z.1.1.2 z.1.2) hm Prod.snd measurable_snd
    convert! hh using 1
    funext z
    simp only [MixedPastNativeConsistentPoint.point,ActualMeanKernel.rowPoint,
      MixedPastNativeConsistentPoint.meanField,MixedPastLiteralPoint.meanField]
  exact (hpoint 1).sub (hpoint 0)

/-- Joint current-time, original old-time, sample, input and output
Borel field for the COMPLETE old-space averaged q-law kernel. -/
theorem kernel_time_measurable (k:ℕ):
    Measurable (fun z:((ℝ≥0×(Fin k→ℝ))×Ω)×(HeatCircle×HeatCircle)=>
      Spatial k z.1.1.1 z.1.1.1 z.1.1.2 (z.1.2,z.2)):=by
  let W:=((ℝ≥0×(Fin k→ℝ))×Ω)×(HeatCircle×HeatCircle)
  have hs:Measurable (fun z:(Fin k→HeatCircle)×W=>
      separated k (z.2.2.2,z.2.1.1.2,z.1)):=
    (separated_measurable k).comp (measurable_snd.snd.snd.prodMk
      (measurable_snd.fst.fst.snd.prodMk measurable_fst))
  have hp:Measurable (fun z:(Fin k→HeatCircle)×W=>
      (((z.2.1.1.1,z.2.1.2),separated k (z.2.2.2,z.2.1.1.2,z.1)),z.2.2.1)):=
    ((measurable_snd.fst.fst.fst.prodMk measurable_snd.fst.snd).prodMk hs).prodMk
      measurable_snd.snd.fst
  have hm:=(difference_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k).comp hp
  have hi:=hm.stronglyMeasurable.integral_prod_left'
    (μ:=Measure.pi (fun _:Fin k=>AddCircle.haarAddCircle))
  have ho:=Complex.continuous_ofReal.measurable.comp hi.measurable
  convert! ho using 1
  unfold MixedPastNativeKernelAverage.spatial
  rfl


local instance mixedPastNativeTimeFields_spaceSigma : MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedPastNativeTimeFields_spaceBorel : BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
local instance mixedPastNativeTimeFields_nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

/-- Actual original Haar columns are jointly Borel in current time,
original old times and sample, including a dependent coefficient. -/
theorem columns_time_measurable (k:ℕ){mass ρ m Upper:ℝ}
    (hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((ℝ≥0×(Fin k→ℝ))×Ω)→EllipticField m Upper)(hc:Measurable c):
    Measurable (fun z:(ℝ≥0×(Fin k→ℝ))×Ω=>
      MixedPastNativeHaarFields.columns
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        k z.1.1 hmass hρ hm (fun p=>c ((z.1.1,p.1),p.2)) (z.1.2,z.2)):=by
  let G:(((ℝ≥0×(Fin k→ℝ))×Ω)×(HeatCircle×HeatCircle))→ℂ:=
    fun z=>Spatial k z.1.1.1 z.1.1.1 z.1.1.2 (z.1.2,z.2)
  have hG:Measurable G:=kernel_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k
  have hbound:∀p:(ℝ≥0×(Fin k→ℝ))×Ω,∃B:ℝ,∀y x,‖G (p,(y,x))‖≤B:=by
    intro p
    exact MixedPastNativeHaarFields.kernel_sections_bounded
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k p.1.1 (p.1.2,p.2)
  have hh:=NativeKernelHaarColumns.columns_measurable hmass hρ hm hG hbound c hc
  convert! hh using 1

/-- The genuine original old-time average of the actual columns is
Borel jointly in current time and sample; no fixed-time-only Fubini
premise is left for the original J energy assembly. -/
theorem average_columns_time_measurable (k:ℕ)(old:Measure (Fin k→ℝ))[SFinite old]
    {mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((ℝ≥0×(Fin k→ℝ))×Ω)→EllipticField m Upper)(hc:Measurable c):
    Measurable (fun z:ℝ≥0×Ω=>∫t:Fin k→ℝ,
      MixedPastNativeHaarFields.columns
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        k z.1 hmass hρ hm (fun p=>c ((z.1,p.1),p.2)) (t,z.2) ∂old):=by
  have hh:=columns_time_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k hmass hρ hm c hc
  have hmap:Measurable (fun z:(ℝ≥0×Ω)×(Fin k→ℝ)=>((z.1.1,z.2),z.1.2)):=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  convert! ((hh.comp hmap).stronglyMeasurable.integral_prod_right' (ν:=old)).measurable using 1

end SHE.MixedPastNativeTimeFields
