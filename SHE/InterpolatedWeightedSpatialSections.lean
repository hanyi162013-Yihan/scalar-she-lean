module

public import SHE.WeightedQuarterSpatialSections
public import SHE.InterpolatedWeightedSpatialMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2800000
noncomputable section

namespace SHE.InterpolatedWeightedSpatialSections
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance weightedJointSpatialSectionsLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance weightedJointSpatialSectionsLocal12 : MeasurableSpace RealL2 := borel _
local instance weightedJointSpatialSectionsLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance weightedJointSpatialSectionsLocal14 : MeasurableSpace CircleL2 := borel _
local instance weightedJointSpatialSectionsLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance weightedJointSpatialSectionsLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance weightedJointSpatialSectionsLocal17 : MeasurableSpace RealHaarInput := borel _
local instance weightedJointSpatialSectionsLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance weightedJointSpatialSectionsLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance weightedJointSpatialSectionsLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

open HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope HistoryQuarterFields QuarterSpatialEvent
  FullResidualInterpolatedWeightedMoments NormalizedKernelSplit

include hIJ₀ hIJ₁ in
/-- A genuine normalized joint kernel moment on almost every old-time
section, for the actual mixed-coefficient joint process. The Gaussian
word moments, adaptive-history exceptional sets and old-score forest
are all discharged. This is the sharp input to the raw signed trace. -/
theorem normalized_quarter_moment (hΛ : 0 ≤ Λ) (hθ : |θ|≤1) (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (hstop : ∀ p i,(L.observations.observations p i).stop ≤ L.terminal p)
    (k : ℕ) :
    ∃ Hf Cf : ℝ,∃ Hs Cs : ℕ → ℝ,0 < Hf ∧ 0 < Cf ∧ (∀ j,0 < Hs j) ∧ (∀ j,0 < Cs j) ∧
    ∀ A : ℝ,(∀ p,(L.observations.observations p 0).target=A) →
      (∀ p,(L.observations.observations p 0).center=p) →
      A ≤ Hf → (∀ j,j < k → A ≤ Hs j) →
    ∀ A0 ν : ℝ,0 ≤ A0 → 0 ≤ ν →
    (∀ p j,j ≤ k → ∀ z,‖iteratedFDeriv ℝ j (L.test p) z‖ ≤ A0*ν^j) →
    ∀ b : ℕ,0 < b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
    ∀ q : ℝ≥0,q ≤ H →
    ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ).base
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ).horizon)),
      active L T k q t →
        ∀ᵐ z : Space ∂(haarAddCircle (T:=2*Real.pi)).prod haarAddCircle,
          let m := actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q
          let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
          WeightedQuarterSpatialEvent.timeMoment L μ T Λ k q m (2*b) (t,z) ≤
            FullResidualPointMoments.momentConstant P k b C0*
              (heatEnvelope (amplitude L P k q Cf (fraction P*P.lower) A0 ν Cs t)
                (quarterTraceTime (R:=ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ)
                  T k q t) (A-q) z)^(2*b) := by
  obtain ⟨Hf,Cf,Hs,Cs,hHf,hCf,hHs,hCs,hspatial⟩ := InterpolatedWeightedSpatialMoments.quarter_spatial_even_moment
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P haP θ L hΛ hθ T hT hages hstop
      (haarAddCircle (T:=2*Real.pi)) k
  refine ⟨Hf,Cf,Hs,Cs,hHf,hCf,hHs,hCs,?_⟩
  intro A hA hx hAHf hAHs A0 ν hA0 hν hjet b hb0 B0 hBDG q hqH
  let m := actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k q
  let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
  let C := FullResidualPointMoments.momentConstant P k b C0
  let ell0 := fraction P*P.lower
  have htarget (p : HeatCircle) (i : Fin 1) : (L.observations.observations p i).target=A := by
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi] using hA p
  have htarget_le (p : HeatCircle) (i : Fin 1) : (L.observations.observations p i).target ≤ A :=
    le_of_eq (htarget p i)
  have hterm (p : HeatCircle) : L.terminal p ≤ A := (L.targets_after p 0).trans (htarget_le p 0)
  have hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2) :=
    ActualInterpolatedMeanFields.actual_mean_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S P haP θ L k q
  apply WeightedQuarterSpatialEvent.normalized_time_sections L μ T A Λ hT hA hx P k q Cf ell0 A0 ν C hCf.le
    (mul_pos (fraction_pos P) P.lower_pos) (FullResidualPointMoments.momentConstant_nonneg P k b C0)
      Cs (fun j => (hCs j).le) m hm (2*b)
  filter_upwards [hspatial A0 ν hA0 hν hjet b hb0 B0 hBDG q hqH
    (fun p i => (htarget_le p i).trans hAHf)] with p hp
  filter_upwards [hp] with t ht
  intro p₀ r hstrict hq
  have hsmall := smallHistory_of_horizon L A hterm htarget_le Hs k hAHs p₀
  filter_upwards [ht hstrict hq hsmall] with y hy
  simpa only [freshAmplitude] using hy.2

end SHE.InterpolatedWeightedSpatialSections
