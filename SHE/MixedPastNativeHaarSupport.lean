module
public import SHE.MixedPastNativeHaarFields
public import SHE.PhysicalOrderedGaps
public import SHE.NativeKernelFiber

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedPastNativeHaarSupport
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeHaarSupport_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeHaarSupport_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeHaarSupport_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeHaarSupport_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeHaarSupport_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeHaarSupport_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastNativeHaarSupport_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeHaarSupport_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeHaarSupport_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

theorem kernel_zero (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(hvq:v≤q)
    (ha:¬QuarterSpatialEvent.active Zero (b:ℝ) k q t)(ω:Ω)(y x:HeatCircle):
    Spatial k q q t (ω,(y,x))=0:=by
  have hnot:¬OrderedGapCoordinates.ordered (q:ℝ) (b:ℝ) k t:=by
    intro ho
    have hh:=(PhysicalOrderedGaps.strict_active_iff_ordered Zero (b:ℝ) (fun _=>rfl)
      (q:ℝ) (by exact_mod_cast hvq) k t 0 (fun _=>0)).mpr ho
    apply ha
    refine ⟨hh.1,?_⟩
    have ht:=ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    exact hh.2.trans_eq ht
  have hp(θ:ℝ)(w:Fin k→HeatCircle):
      MixedPastNativeConsistentPoint.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q q (separated k (x,t,w)) y ω=0:=by
    let L:=Base (θ,(U ω,Dir ω))
    have hnot':¬(StrictHistory L k (separated k (x,t,w)) ∧
        (q:ℝ)<(carrier L k).terminal (separated k (x,t,w))):=by
      intro hh
      exact hnot ((PhysicalOrderedGaps.strict_active_iff_ordered L (b:ℝ) (fun _=>rfl)
        (q:ℝ) (by exact_mod_cast hvq) k t x w).mp hh)
    unfold MixedPastNativeConsistentPoint.point
    rw [ActualMeanKernel.rowPoint_same]
    by_cases hh:StrictHistory L k (separated k (x,t,w))
    · have hqt:¬(q:ℝ)<(carrier L k).terminal (separated k (x,t,w)):=fun h=>hnot' ⟨hh,h⟩
      change ActualMeanKernel.point L k _ _ _ _=0
      simp only [ActualMeanKernel.point,if_neg hqt]
    · exact ActualMeanKernel.point_zero_of_not_strict L k _ _ _ _ hh
  unfold MixedPastNativeKernelAverage.spatial MixedPastNativeKernel.difference
  simp only [hp,sub_self,integral_zero,Complex.ofReal_zero]

/-- The realized countable columns have the literal inactive support;
zero extension is therefore an equality of the actual field. -/
theorem columns_zero (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(hvq:v≤q)
    (ha:¬QuarterSpatialEvent.active Zero (b:ℝ) k q t)
    {mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper)(ω:Ω):
    MixedPastNativeHaarFields.columns
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k q hmass hρ hm c (t,ω)=0:=by
  have hz:=NativeRandomKernel.integralOperator_eq_zero_of_fiber (Spatial k q q t) ω
    (fun y x=>kernel_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q t hvq ha ω y x)
  ext j
  simp only [MixedPastNativeHaarFields.columns_apply,hz,ContinuousLinearMap.zero_apply,map_zero,
    lp.coeFn_zero,Pi.zero_apply]
  exact Filter.EventuallyEq.rfl

end SHE.MixedPastNativeHaarSupport

