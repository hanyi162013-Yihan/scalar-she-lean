module

public import SHE.MixedPastTerminalCovarianceSpatialFields
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

namespace SHE.MixedPastTerminalCovarianceAverages
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

/-- Literal original old-space average, with the sample and output
root still retained for the subsequent original old-time average. -/
def oldSpaceAverage (k:ℕ) (ζ:ℝ) (z:(Fin (k+1)→ℝ)×(Ω×HeatCircle)):ℝ:=
  ∫w,Point k ζ z.1 (z.2,w) ∂Measure.pi (fun _:Fin (k+1)=>haarAddCircle)

local notation "Avg"=>oldSpaceAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- True joint Borel old-time/sample/output field BEFORE choosing any
exceptional time section or applying the time Minkowski inequality. -/
theorem oldSpaceAverage_measurable (k:ℕ) (ζ:ℝ):Measurable (Avg k ζ):=by
  let hist:=fun z:((Fin (k+1)→ℝ)×(Ω×HeatCircle))×(Fin (k+1)→HeatCircle)=>
    separated (k+1) (z.1.2.2,z.1.1,fun i=>z.2 i+z.1.2.2)
  have hh:Measurable hist:=(separated_measurable (k+1)).comp
    (measurable_fst.snd.snd.prodMk (measurable_fst.fst.prodMk
      (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add measurable_fst.snd.snd))))
  have hfull:Measurable (fun z:((Fin (k+1)→ℝ)×(Ω×HeatCircle))×(Fin (k+1)→HeatCircle)=>
      Point k ζ z.1.1 (z.1.2,z.2)):=by
    convert! (MixedPastTerminalCovarianceFields.active_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      (k+1) ζ).comp (hh.prodMk measurable_fst.snd.fst) using 1
  exact hfull.stronglyMeasurable.integral_prod_right'.measurable

/-- Inactive ORIGINAL old-time histories vanish literally; individual
Gaussian assignments are not incorrectly claimed to vanish. -/
theorem oldSpaceAverage_zero (k:ℕ) (ζ:ℝ) (t:Fin (k+1)→ℝ)
    (hinactive:¬(StrictHistory Zero (k+1) (anchor (k+1) t) ∧
      (v:ℝ)<(carrier Zero (k+1)).terminal (anchor (k+1) t))):
    ∀y:Ω×HeatCircle,Avg k ζ (t,y)=0:=by
  intro y
  have hn:¬StrictHistory Zero (k+1) (anchor (k+1) t):=by
    intro hp
    apply hinactive
    refine ⟨hp,?_⟩
    have hnode:(carrier Zero (k+1)).terminal (anchor (k+1) t)=
        (anchor (k+1) t).2.1:=ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
    rw [hnode]
    exact hp.2.1
  have hz(w:Fin (k+1)→HeatCircle):Point k ζ t (y,w)=0:=by
    have hnot:¬StrictHistory Zero (k+1) (separated (k+1) (y.2,t,fun i=>w i+y.2)):=by
      intro hp
      apply hn
      exact (FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) (fun _=>rfl)
        (k+1) t y.2 0 _ (fun _=>0)).mp hp
    exact ite_eq_right hnot
  unfold oldSpaceAverage
  simp_rw [hz]
  exact integral_zero _ _

end SHE.MixedPastTerminalCovarianceAverages
