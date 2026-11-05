module

public import SHE.ActualBaselineRelativeFields
public import SHE.InactivePhysicalAverage
public import SHE.ActualInterpolatedMeanFields
public import SHE.ActualBaselineMarkFields
public import SHE.ControlledScoreRates
public import SHE.ForestTranslation
public import SHE.FullResidualInterpolatedWeightedMoments
public import SHE.JointInterpolationFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace SHE.ActualBaselineTimeFields
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance fullResidualInterpolatedWeightedLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance fullResidualInterpolatedWeightedLocal12 : MeasurableSpace RealL2 := borel _
local instance fullResidualInterpolatedWeightedLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal14 : MeasurableSpace CircleL2 := borel _
local instance fullResidualInterpolatedWeightedLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance fullResidualInterpolatedWeightedLocal17 : MeasurableSpace RealHaarInput := borel _
local instance fullResidualInterpolatedWeightedLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullResidualInterpolatedWeightedLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullResidualInterpolatedWeightedLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) HeatCircle 1)


open HistoryProductMeasure ActualMeanKernel ProfilePointwise ProfileStability ControlledScoreRates
  ActualBaselineRelativeFields OrderedHeatForests

/-- Joint measurability in original old times, sample, output root and
all relative old insertion sites, before old-space averaging. -/
theorem relative_point_time_measurable (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (q : ℝ≥0) :
    Measurable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q z.1.1 (z.1.2,z.2)) := by
  let p : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)→History HeatCircle k :=
    fun z=>separated k (z.1.2.2,z.1.1,fun i=>z.2 i+z.1.2.2)
  have hsites : Measurable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      fun i=>z.2 i+z.1.2.2) :=
    Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add measurable_fst.snd.snd)
  have hp : Measurable p := (separated_measurable k).comp
    (measurable_fst.snd.snd.prodMk (measurable_fst.fst.prodMk hsites))
  have hM := ActualInterpolatedMeanFields.actual_mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S P haP θ L k q
  have hm : Measurable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      FullResidualInterpolatedWeightedMoments.actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S P haP θ L k q z.1.2.1 (p z)) := by
    convert! hM.comp (measurable_fst.snd.fst.prodMk hp) using 1
  have hdb : Measurable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      ControlledBaselineAssignments.derivatives P haP Λ (embed u₀) (embed (v₀-u₀)) θ L k (p z)) := by
    apply Measurable.of_eval
    intro j
    convert! (ControlledProfile.derivative_measurable P hΛ (embed u₀) (embed (v₀-u₀)) hsmallPoint).comp
      ((((lower_measurable L k j).comp hp).prodMk ((space_measurable k j).comp hp)).prodMk measurable_const) using 1
  exact ActualBaselineMarkFields.point_variable_measurable L
    (referenceProfile P Λ (embed u₀) (embed (v₀-u₀)))
    (referenceProfile_measurable P Λ (embed u₀) (embed (v₀-u₀))) k p hp
    (fun _=>q) measurable_const _ hm _ hdb

/-- Genuine original old-time/sample/output measurability after the
whole old spatial average, ready for Hilbert Minkowski in old time. -/
theorem averaged_point_time_measurable (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (q : ℝ≥0) :
    Measurable (fun z : (Fin k→ℝ)×(Ω×HeatCircle)=>∫ w : Fin k→HeatCircle,
      relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q z.1 (z.2,w)
        ∂Measure.pi (fun _=>haarAddCircle)) :=
  (relative_point_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P haP θ L hΛ hsmallPoint k q).stronglyMeasurable.integral_prod_right'.measurable

/-- Relative old locations are an exact change of variables in the
literal baseline mark, including every original old insertion site. -/
theorem relative_average_eq (k : ℕ) (q : ℝ≥0) (t : Fin k→ℝ) (ω : Ω) (x : HeatCircle) :
    (∫ w : Fin k→HeatCircle,
      relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q t ((ω,x),w)
        ∂Measure.pi (fun _=>haarAddCircle))=
    ∫ w : Fin k→HeatCircle,
      ActualBaselineMarkFields.point L (referenceProfile P Λ (embed u₀) (embed (v₀-u₀)))
        k q (ControlledBaselineAssignments.derivatives P haP Λ (embed u₀) (embed (v₀-u₀)) θ L k (separated k (x,t,w)))
        (FullResidualInterpolatedWeightedMoments.actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S P haP θ L k q ω (separated k (x,t,w))) (separated k (x,t,w))
      ∂Measure.pi (fun _=>haarAddCircle) := by
  exact (relativeShift_preserving k x).integral_comp'
    (fun w : Fin k→HeatCircle=>
      ActualBaselineMarkFields.point L (referenceProfile P Λ (embed u₀) (embed (v₀-u₀)))
        k q (ControlledBaselineAssignments.derivatives P haP Λ (embed u₀) (embed (v₀-u₀)) θ L k (separated k (x,t,w)))
        (FullResidualInterpolatedWeightedMoments.actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
          I₀ I₁ u₀ v₀ S P haP θ L k q ω (separated k (x,t,w))) (separated k (x,t,w)))

/-- Inactive original time sections vanish exactly. This is not an
assumption about a spatial representative or a Gaussian exceptional set. -/
theorem relative_point_zero_of_not_strict (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (q : ℝ≥0) (t : Fin k→ℝ)
    (hp : ¬StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0)))
    (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) :
    relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q t z=0 := by
  classical
  have hn : ¬StrictHistory L k (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)) := by
    intro hh
    exact hp ((FixedHistoryTimeFactors.strict_sections L T hT k t z.1.2 0 _ (fun _=>0)).mp hh)
  dsimp only [relativePoint]
  unfold ActualBaselineMarkFields.point
  split_ifs
  · obtain ⟨j,hj⟩ := exists_zero_direction_of_not_strict L
      ((carrier L k).observations.observations (separated k (z.1.2,t,fun i=>z.2 i+z.1.2))) k
      (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)) hn
    have hz (x : Fin k→WordRecursion.State (1+k)) :
        (∏ l,MeasurableGaussianScores.secondScore
          (covariances L ((carrier L k).observations.observations (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)))
            (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) k (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)) l)
          (directions L ((carrier L k).observations.observations (separated k (z.1.2,t,fun i=>z.2 i+z.1.2))) k
            (separated k (z.1.2,t,fun i=>z.2 i+z.1.2)) l) (x l))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hj,secondScore_zero_direction]
    simp only [baselineMark,omittedAverage,WeightedBorelAverage.average,hz,zero_mul,integral_zero,
      gaussianAverage,mul_zero,Finset.sum_const_zero,neg_zero]
  · rfl

end SHE.ActualBaselineTimeFields
