module

public import SHE.MixedPastTerminalSources
public import SHE.MixedPastTerminalPairedFields
public import SHE.JointCurrentDifference
public import SHE.ControlledThetaRelativeWord
public import SHE.ControlledThetaRelativeDerivative
public import SHE.ControlledTerminalPairedFields
public import SHE.JointHistoryFields
public import SHE.WeightedRowTimeShift
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastTerminalSourceFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

local notation "DataU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DataV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S


open MixedPastTerminalPairedFields
local notation "Cur"=>current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "UU"=>Function.uncurry S.first
local notation "VV"=>Function.uncurry S.second


/-- The extracted sources in the ACTUAL finite endpoint comparison are
jointly Borel before source/word correlation is estimated. -/
theorem source_measurable (k:ℕ) (choices:List (Fin k×Fin (k+1))) (ν χ:ℝ) (i:Fin (k+1)):
    Measurable (fun z:History X k×Ω=>MixedPastTerminalSources.source
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k choices ν χ i z.1 z.2):=by
  have hc(second:Bool):Measurable (fun z:History X k×Ω=>Cur second k z.1 z.2):=
    MixedPastTerminalPairedFields.current_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm second k
  have hu:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:Measurable Dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hbas(η:ℝ)(j:Fin k):Measurable (fun z:History X k×Ω=>baseline (Base (η,(U z.2,Dir z.2))) k z.1 j):=by
    have hp:Measurable (fun z:History X k×Ω=>(η,(U z.2,Dir z.2))):=
      measurable_const.prodMk ((hu.comp measurable_snd).prodMk (hd.comp measurable_snd))
    have hz:Measurable (fun z:History X k×Ω=>(lower Zero k z.1 j,space k z.1 j)):=
      ((lower_measurable Zero k j).comp measurable_fst).prodMk ((space_measurable k j).comp measurable_fst)
    have hh:=(ControlledThetaWordFields.coefficient_joint_measurable P Λ v).comp (hp.prodMk hz)
    convert! hh using 1
    funext z
    unfold baseline
    rw [ControlledThetaPhysicalGeometry.lower_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (η,(U z.2,Dir z.2)) (0,(0,0)) k z.1]
    rfl
  have hcoord(j:Fin (1+k)):Measurable (fun z:History X k×Ω=>Cur true k z.1 z.2 j-Cur false k z.1 z.2 j):=
    ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable.comp (hc true)).sub
      ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable.comp (hc false))
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [MixedPastTerminalSources.source,PairedAssignedTelescope.sources,Fin.cases_zero]
    exact (measurable_const.min (((GaussianCoordinates.projection (rootSelector k (fun i=>i))).continuous.measurable.comp
      ((hc true).sub (hc false))).norm.const_mul ν)).pow_const χ
  · simp only [MixedPastTerminalSources.source,PairedAssignedTelescope.sources,Fin.cases_succ,
      PairedRoughWordMoments.source]
    split_ifs with hb
    · unfold NormalizedPairedLeaf.source
      exact (measurable_const.mul ((continuous_abs.measurable.comp (hcoord _)).pow_const χ)).add
        ((continuous_abs.measurable.comp ((hbas 1 j).sub (hbas 0 j))).pow_const (χ/P.exponent))
    · exact (continuous_abs.measurable.comp (hcoord _)).pow_const χ

end SHE.MixedPastTerminalSourceFields
