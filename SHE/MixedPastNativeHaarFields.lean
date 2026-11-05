module
public import SHE.MixedPastNativeHaarEnergy
public import SHE.NativeKernelHaarColumns

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedPastNativeHaarFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeHaarFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeHaarFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeHaarFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeHaarFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeHaarFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeHaarFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastNativeHaarFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeHaarFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeHaarFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- The literal q-law physical kernel is jointly Borel in original old
times, sample, input and output, before any Hilbert realization. -/
theorem kernel_joint_measurable (k:ℕ)(q:ℝ≥0):
    Measurable (fun z:((Fin k→ℝ)×Ω)×(HeatCircle×HeatCircle)=>Spatial k q q z.1.1 (z.1.2,z.2)):=by
  have hs:Measurable (fun z:(Fin k→HeatCircle)×(((Fin k→ℝ)×Ω)×(HeatCircle×HeatCircle))=>
      separated k (z.2.2.2,z.2.1.1,z.1)):=
    (separated_measurable k).comp (measurable_snd.snd.snd.prodMk
      (measurable_snd.fst.fst.prodMk measurable_fst))
  have hd:=MixedPastNativeKernel.difference_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q q
  have hp:Measurable (fun z:(Fin k→HeatCircle)×(((Fin k→ℝ)×Ω)×(HeatCircle×HeatCircle))=>
      ((z.2.1.2,separated k (z.2.2.2,z.2.1.1,z.1)),z.2.2.1)):=
    (measurable_snd.fst.snd.prodMk hs).prodMk measurable_snd.snd.fst
  have hm:=hd.comp hp
  have hi:=hm.stronglyMeasurable.integral_prod_left'
    (μ:=Measure.pi (fun _:Fin k=>AddCircle.haarAddCircle))
  have ho:=Complex.continuous_ofReal.measurable.comp hi.measurable
  convert! ho using 1
  unfold MixedPastNativeKernelAverage.spatial
  rfl

theorem kernel_sections_bounded (k:ℕ)(q:ℝ≥0):
    ∀p:(Fin k→ℝ)×Ω,∃B:ℝ,∀y x,‖Spatial k q q p.1 (p.2,(y,x))‖≤B:=by
  intro p
  obtain ⟨B,hB,hb⟩:=MixedPastNativeSpatialFields.bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q q p.1
  exact ⟨B,hb p.2⟩

/-- Genuine countable native Bessel/Haar columns, retaining the
original old-time coordinates and the actual dependent coefficient. -/
def columns (k:ℕ)(q:ℝ≥0){mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper) : ((Fin k→ℝ)×Ω)→NativeKernelHaarColumns.Space :=
  NativeKernelHaarColumns.columns hmass hρ hm
    (kernel_joint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q)
    (kernel_sections_bounded 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q) c

local notation "Columns"=>columns
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

@[simp] theorem columns_apply (k:ℕ)(q:ℝ≥0){mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper)(p:(Fin k→ℝ)×Ω)(j:HaarNode):
    Columns k q hmass hρ hm c p j=
      OneInputOperator.besselHalf mass ρ hmass hρ
        (NativeRandomKernel.integralOperator (Spatial k q q p.1) p.2
          (CircleNormalization.push (globalHaarColumn j (c p).1))) := rfl

theorem columns_measurable (k:ℕ)(q:ℝ≥0){mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper)(hc:Measurable c):
    @Measurable _ NativeKernelHaarColumns.Space _ (borel _) (Columns k q hmass hρ hm c):=
  NativeKernelHaarColumns.columns_measurable hmass hρ hm _ _ c hc

/-- Its Hilbert norm is exactly the original countable Haar trace. -/
theorem columns_norm_sq (k:ℕ)(q:ℝ≥0){mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper)(p:(Fin k→ℝ)×Ω):
    ‖Columns k q hmass hρ hm c p‖^2=
      ∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ
        (NativeRandomKernel.integralOperator (Spatial k q q p.1) p.2
          (CircleNormalization.push (globalHaarColumn j (c p).1)))‖^2 :=
  HilbertColumns.norm_sq _

end SHE.MixedPastNativeHaarFields

