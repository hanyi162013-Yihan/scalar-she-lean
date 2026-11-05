module

public import SHE.SharpJointRowDensityMoments
public import SHE.JointHistoryFields
public import SHE.HistoryQuarterFields
public import SHE.PhysicalHistoryHorizon

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.MixedJointSpatialMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance mixedJointSpatialMomentsLocal11 : Fact (0<2*π) := ⟨by positivity⟩
local instance mixedJointSpatialMomentsLocal12 : MeasurableSpace RealL2 := borel _
local instance mixedJointSpatialMomentsLocal13 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedJointSpatialMomentsLocal14 : MeasurableSpace CircleL2 := borel _
local instance mixedJointSpatialMomentsLocal15 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedJointSpatialMomentsLocal16 : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance mixedJointSpatialMomentsLocal17 : MeasurableSpace RealHaarInput := borel _
local instance mixedJointSpatialMomentsLocal18 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedJointSpatialMomentsLocal19 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedJointSpatialMomentsLocal20 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1) X 1)

open HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope HistoryQuarterFields
  MixedNativeJointRowDensityMoments

include hIJ₀ hIJ₁ in
/-- The actual mixed joint stopped flow satisfies sharp spatially
averaged moments at the history-dependent quarter row. All point moment,
old-score forest, Borel and Fubini inputs are derived. Each Hölder block
keeps its true minimum gap. Horizons and forest constants are chosen
before the current time and moment parameters. -/
theorem quarter_spatial_even_moment (hΛ : 0 ≤ Λ) (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∃ Hf Cf : ℝ,∃ Hs Cs : ℕ → ℝ,0 < Hf ∧ 0 < Cf ∧ (∀ j,0 < Hs j) ∧ (∀ j,0 < Cs j) ∧
    ∀ A0 ν : ℝ,0 ≤ A0 → 0 ≤ ν →
    (∀ p j,j ≤ k → ∀ z,‖iteratedFDeriv ℝ j (L.test p) z‖ ≤ A0*ν^j) →
    ∀ b : ℕ,0 < b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
    ∀ q : ℝ≥0,q ≤ H →
    (∀ p i,(L.observations.observations p i).target ≤ Hf) →
    ∀ᵐ p ∂ρ,∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1).base
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1).horizon)),
      let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
      let r := rowTime L k q p₀
      let m := actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP L k q
      let D := freshAmplitude L k q Cf (fraction P*P.lower)
        (fun z => SharpWordTimeScale.total L P k z q A0 ν)
      let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
      ∀ hp : StrictHistory L k p₀,(q:ℝ) < (carrier L k).terminal p₀ → SmallHistory L Hs k p₀ →
        ∀ᵐ y : HeatCircle ∂haarAddCircle,
          Integrable (fun ω => ‖rowSpatial L k q r m t ω y p‖^(2*b)) μ ∧
          (∫ ω,‖rowSpatial L k q r m t ω y p‖^(2*b) ∂μ) ≤
            PhysicalOffsetPointMoments.momentConstant P k b C0*
              (D p₀*massBudget L k p₀ (timeWeight L (fraction P*P.lower) Cs k p₀) r y)^(2*b) := by
  obtain ⟨Hf,Cf,hHf,hCf,hpoint⟩ := SharpMixedNativeJointRowDensityMoments.row_point_even_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P haP L hΛ hages ρ k
  obtain ⟨Hs,Cs,hHs,hCs,hspatial⟩ := row_spatial_history_moment (Ω:=Ω) L
  refine ⟨Hf,Cf,Hs,Cs,hHf,hCf,hHs,hCs,?_⟩
  intro A0 ν hA0 hν hjet b hb0 B0 hBDG q hqH hsmall
  let c := referenceProfile P Λ (embed u₀) (embed (v₀-u₀))
  let ell0 := fraction P*P.lower
  let m := actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP L k q
  let timeScale := fun z => SharpWordTimeScale.total L P k z q A0 ν
  let D := freshAmplitude L k q Cf ell0 timeScale
  let C0 := (NativeHybridMoments.momentConstant (b*(k+2)) B0 κ M)^P.exponent
  let C := PhysicalOffsetPointMoments.momentConstant P k b C0
  have hell0 : 0 < ell0 := mul_pos (fraction_pos P) P.lower_pos
  have hcb (z : Domain) : ell0 ≤ c z ∧ c z ≤
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1).reference z :=
    ⟨(referenceProfile_bounds P Λ (embed u₀) (embed (v₀-u₀)) z).1,
      (referenceProfile_bounds P Λ (embed u₀) (embed (v₀-u₀)) z).2.trans
        ((half_le_self P.lower_pos.le).trans (ControlledProfile.profile_bounds P Λ (embed u₀) (embed (v₀-u₀)) (1,z)).1)⟩
  have hm : Measurable (fun z : Ω × History X k => m z.1 z.2) := by
    exact (MixedNativeJointHistory.evaluate_fixed_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (carrier L k).observations q).comp (measurable_snd.prodMk measurable_fst)
  have hterm (p : X) : L.terminal p ≤ Hf := (L.targets_after p 0).trans (hsmall p 0)
  have hpoint' : ∀ᵐ p ∂historyMeasure
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) 1) ρ k,
      ∀ᵐ y : HeatCircle ∂haarAddCircle,StrictHistory L k p ∧ rowTime L k q p < (carrier L k).terminal p →
        (∫ ω,|rowPoint L k q (rowTime L k q p) (m ω) p y|^(2*b) ∂μ) ≤
          C*(D p*globalDensity L c k p (rowTime L k q p) y)^(2*b) := by
    filter_upwards [hpoint] with p hp
    by_cases ha : StrictHistory L k p ∧ rowTime L k q p < (carrier L k).terminal p
    · have hq := (rowTime_lt_iff L k q p).mp ha.2
      have hages' := carrier_age_le L Hf hterm hsmall k p (q.2.trans (le_rowTime L k q p))
      filter_upwards [hp q hqH hq ha.1 (rowTime L k q p) (le_rowTime L k q p) ha.2 hages'] with y hy
      intro _
      exact (hy A0 ν hA0 hν (hjet (rootParameter k p)) b hb0 B0 hBDG).2
    · exact ae_of_all _ (fun _ h => False.elim (ha h))
  have h := hspatial μ T hT c (referenceProfile_measurable P Λ (embed u₀) (embed (v₀-u₀)))
    hell0 hcb hages ρ k m hm q (rowTime L k q) (rowTime_measurable L k q)
    (rowTime_replaceSpace L k q) D
    (freshAmplitude_measurable L k q Cf ell0 timeScale (SharpWordTimeScale.total_measurable L P k q A0 ν))
    (freshAmplitude_nonneg L k q Cf ell0 timeScale (fun p => SharpWordTimeScale.total_nonneg L P k p q A0 ν))
    (freshAmplitude_replaceSpace L k q Cf ell0 timeScale (fun p x => SharpWordTimeScale.total_replaceSpace L P k p q A0 ν x))
    C (PhysicalOffsetPointMoments.momentConstant_nonneg P k b C0) b hb0 hpoint'
  filter_upwards [h] with p hp
  filter_upwards [hp] with t ht
  intro p₀ r m' D' C0' hstrict hq hhist
  exact ht hstrict ((rowTime_lt_iff L k q p₀).mpr hq) hhist

end SHE.MixedJointSpatialMoments

