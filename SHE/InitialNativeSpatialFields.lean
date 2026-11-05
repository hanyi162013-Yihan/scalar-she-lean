module

public import SHE.InitialSpatialFields
public import SHE.InitialNativeWordFields
public import SHE.InitialTerminalFibre
public import SHE.ZeroDirectionProfile
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.RelativePairedCurrent
public import SHE.PairedFamilyFields
public import SHE.MovingNativeFields
public import SHE.ShiftedHistoryMeasure
public import SHE.MixedPairedMovingSection
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPastTerminalPairedLinearEnergy
public import SHE.MixedPairedCurrentClock
public import SHE.MixedPastTerminalTimeFields
public import SHE.ControlledTerminalRMSMass
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.InitialNativeSpatialFields
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance initialNativeSpatialFields_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialNativeSpatialFields_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance initialNativeSpatialFields_instance3 : MeasurableSpace RealL2 := borel _
local instance initialNativeSpatialFields_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance initialNativeSpatialFields_instance5 : MeasurableSpace CircleL2 := borel _
local instance initialNativeSpatialFields_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance initialNativeSpatialFields_instance7 : MeasurableSpace RealHaarInput := borel _
local instance initialNativeSpatialFields_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialNativeSpatialFields_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialNativeSpatialFields_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance initialNativeSpatialFields_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance initialNativeSpatialFields_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth CutoffWordLevel
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient) (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (embed u₀,0)
local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "ZZ" T:max=>ControlledScalarReference.observations T
local notation "K" α:max T:max=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ α 0 T bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (embed u₀,0)
local notation "Zero" T:max=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ 0 0 T bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,0)

def value (k:ℕ) (T:Icc (0:ℝ) (h:ℝ)) (y:Ω×HeatCircle):ℝ:=
  InitialSpatialFields.value R F hF hFm Λ (DU).physicalState (DV).physicalState
    (DU).physicalField (DV).physicalField k T y
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

theorem value_measurable (k:ℕ):Measurable (fun z:Icc (0:ℝ) (h:ℝ)×(Ω×HeatCircle)=>Value k z.1 z.2):=
  InitialSpatialFields.value_measurable R F hF hFm Λ (DU).physicalState (DV).physicalState
    (DU).physicalField (DV).physicalField (DU).physicalState_measurable (DV).physicalState_measurable
    (DU).physicalField_measurable (DV).physicalField_measurable k

/-- ONE actual initial sample event gives EVERY output time and EVERY
retained output position, with the original old-history measure. -/
theorem value_initial_ae:
    ∀ᵐω ∂μ,∀T:Icc (0:ℝ) (h:ℝ),∀k:ℕ,∀x:HeatCircle,
      HistoryProductMeasure.rootAverage
        (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (0,0)) k
        (fun a=>MixedPastTerminalEndpointWord.wordDifference
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le
          (ZZ (⟨T,T.2.1⟩:ℝ≥0)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k a.2 a.1) (ω,x)=
        Value k T (ω,x):=by
  filter_upwards [InitialNativeWordFields.point_initial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T k x
  let TN:ℝ≥0:=⟨T,T.2.1⟩
  let Q:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 TN bot_le (0,0)
  let W:=fun a:Ω×History HeatCircle k=>MixedPastTerminalEndpointWord.wordDifference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 TN bot_le
      (ZZ TN) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k a.2 a.1
  have hs:∀ω p,p∉HistoryHorizonIntegration.box Q.horizon k→W (ω,p)=0:=by
    intro ω p hp
    have hn:¬PhysicalParentGeometry.StrictHistory (Zero TN) k p:=by
      intro ht
      exact hp (HistoryHorizonIntegration.strict_mem (Zero TN) Q.horizon (fun _=>le_rfl) k p ht)
    simp only [W,MixedPastTerminalEndpointWord.wordDifference,if_neg hn]
  change HistoryProductMeasure.rootAverage Q k W (ω,x)=_
  rw [InitialSpatialFields.root_average_horizon R (Q:=Q) rfl T.2.2 k W hs]
  unfold HistoryProductMeasure.rootAverage value InitialSpatialFields.value
  apply integral_congr_ae
  filter_upwards with t
  apply integral_congr_ae
  filter_upwards with w
  exact hω T k _

end SHE.InitialNativeSpatialFields
