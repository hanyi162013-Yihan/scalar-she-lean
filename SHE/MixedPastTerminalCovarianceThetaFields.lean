module

public import SHE.MixedPastTerminalCovarianceAverages
public import SHE.MeanThetaAverage
public import SHE.TerminalCovarianceTimeIntegral
public import SHE.MixedPastFiniteTerminalMass

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastTerminalCovarianceThetaFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "G"=>MixedPastTerminalCovarianceFields.active 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "MActual"=>MixedPastTerminalCovarianceFields.mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point"=>MixedPastTerminalCovarianceSpatialFields.relativePoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Avg"=>MixedPastTerminalCovarianceAverages.oldSpaceAverage
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Genuine joint interpolation/old-time/sample/output measurability;
no uncountable intersection of chosen exceptional sets is used. -/
theorem oldSpaceField_measurable (k:ℕ):
    Measurable (fun z:ℝ×((Fin (k+1)→ℝ)×(Ω×HeatCircle))=>Avg k z.1 z.2):=by
  classical
  let hist:=fun z:(ℝ×((Fin (k+1)→ℝ)×(Ω×HeatCircle)))×(Fin (k+1)→HeatCircle)=>
    separated (k+1) (z.1.2.2.2,z.1.2.1,fun i=>z.2 i+z.1.2.2.2)
  have hhist:Measurable hist:=(separated_measurable (k+1)).comp
    (measurable_fst.snd.snd.snd.prodMk (measurable_fst.snd.fst.prodMk
      (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add
        measurable_fst.snd.snd.snd))))
  have hp:Measurable (fun z:(ℝ×((Fin (k+1)→ℝ)×(Ω×HeatCircle)))×(Fin (k+1)→HeatCircle)=>
      MixedPastTerminalFiniteCovariance.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
        (k+1) 1 0 1 z.1.1 (hist z) z.1.2.2.1):=
    MixedPastTerminalFiniteCovariance.point_variable_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      (k+1) hist hhist _ measurable_fst.snd.snd.fst
      (fun _=>1) (fun _=>0) (fun _=>1) (fun z=>z.1.1)
      measurable_const measurable_const measurable_const measurable_fst.fst
  have hactive:Measurable (fun z:(ℝ×((Fin (k+1)→ℝ)×(Ω×HeatCircle)))×(Fin (k+1)→HeatCircle)=>
      G (k+1) z.1.1 (hist z) z.1.2.2.1):=
    hp.ite ((strictHistory_measurableSet Zero (k+1)).preimage hhist) (measurable_const (a:=(0:ℝ)))
  convert! (hactive.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _:Fin (k+1)=>haarAddCircle (T:=2*Real.pi)))).measurable using 1

/-- Actual original old-space THEN old-time average at each covariance
interpolation parameter. -/
def timeAverage (k:ℕ) (z:ℝ×(Ω×HeatCircle)):ℝ:=
  ∫t,Avg k z.1 (t,z.2) ∂Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (v:ℝ) (b:ℝ)))

local notation "TimeAvg"=>timeAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

theorem timeAverage_measurable (k:ℕ):Measurable (TimeAvg k):=by
  have hm:Measurable (fun z:(ℝ×(Ω×HeatCircle))×(Fin (k+1)→ℝ)=>
      (z.1.1,(z.2,z.1.2))):=measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)
  exact ((oldSpaceField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k).comp hm).stronglyMeasurable.integral_prod_right'.measurable

/-- The literal covariance FTC parameter is averaged only after the
original old-space and old-time averages. -/
def thetaAverage (k:ℕ) (y:Ω×HeatCircle):ℝ:=
  ∫ζ,TimeAvg k (ζ,y) ∂MeanThetaAverage.thetaMeasure

theorem thetaAverage_measurable (k:ℕ):
    Measurable (thetaAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k):=
  (timeAverage_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k).stronglyMeasurable.integral_prod_left'.measurable

end SHE.MixedPastTerminalCovarianceThetaFields
