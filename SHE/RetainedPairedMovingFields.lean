module

public import SHE.MovingPairedFields
public import SHE.RetainedPairedMovingSection
public import SHE.RootHistoryFubini
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

namespace SHE.RetainedPairedMovingFields
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingTerminalSpatialFields_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingTerminalSpatialFields_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingTerminalSpatialFields_instance3 : MeasurableSpace RealL2 := borel _
local instance movingTerminalSpatialFields_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingTerminalSpatialFields_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingTerminalSpatialFields_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingTerminalSpatialFields_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingTerminalSpatialFields_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingTerminalSpatialFields_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingTerminalSpatialFields_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingTerminalSpatialFields_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingTerminalSpatialFields_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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
open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm (0,(0,0))
local notation "Abs"=>fun v=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "DataU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DataV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "RC"=>RelativePairedCurrent.current P haP Λ h Z htarget hstop F hF hFm
local notation "RP"=>MovingPairedFields.relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

/-- The literal output position is retained; only original old times and
old locations are averaged. -/
def value (ν χ:ℝ) (v:ℝ≥0) (k:ℕ) (y:Ω×HeatCircle):ℝ:=
  ∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,
    RP k ν χ v (HistoryProductMeasure.separated k (y.2,t,fun j=>w j+y.2)) y.1
    ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem value_measurable (ν χ:ℝ) (k:ℕ):Measurable (fun z:ℝ≥0×(Ω×HeatCircle)=>Value ν χ z.1 k z.2):=by
  have hs:Measurable (fun z:((ℝ≥0×(Ω×HeatCircle))×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      HistoryProductMeasure.separated k (z.1.1.2.2,z.1.2,fun j=>z.2 j+z.1.1.2.2)):=by
    apply (HistoryProductMeasure.separated_measurable k).comp
    exact measurable_fst.fst.snd.snd.prodMk (measurable_fst.snd.prodMk
      (Measurable.of_eval (fun j=>(measurable_pi_apply j).comp measurable_snd |>.add measurable_fst.fst.snd.snd)))
  have hm:Measurable (fun z:((ℝ≥0×(Ω×HeatCircle))×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      RP k ν χ z.1.1.1 (HistoryProductMeasure.separated k (z.1.1.2.2,z.1.2,fun j=>z.2 j+z.1.1.2.2)) z.1.1.2.1):=by
    exact (MovingPairedFields.relativePoint_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k ν χ).comp
      ((measurable_subtype_coe.comp measurable_fst.fst.fst).prodMk (hs.prodMk measurable_fst.fst.snd.fst))
  exact (hm.stronglyMeasurable.integral_prod_right'.measurable.stronglyMeasurable.integral_prod_right').measurable

theorem value_absolute (ν χ:ℝ) (v:ℝ≥0) (k:ℕ) (y:Ω×HeatCircle):
    Value ν χ v k y=HistoryProductMeasure.rootAverage
      (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v (v+h) le_self_add (0,0)) k
      (fun a=>MixedPastTerminalPairedWord.point
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v (v+h) le_self_add
        (ZT v) (HT v) (HS v) F hF hFm k ν χ a.2 a.1) y:=by
  unfold HistoryProductMeasure.rootAverage
  change Value ν χ v k y=(∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,
    MixedPastTerminalPairedWord.point
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k ν χ
      (HistoryProductMeasure.separated k (y.2,t,fun j=>w j+y.2)) y.1
      ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
      ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))))
  have he:MeasurableEmbedding (fun t:Fin k→ℝ=>fun j=>t j+(v:ℝ)):=
    (Homeomorph.addRight (fun _:Fin k=>(v:ℝ))).measurableEmbedding
  rw [←(MixedPairedClockIntegrals.pi_translation (h:=h) v k).integral_comp he]
  apply integral_congr_ae
  filter_upwards with t
  apply integral_congr_ae
  filter_upwards with w
  rw [←PairedTimeTranslation.separated_shift (v:=(v:ℝ)) k y.2 t (fun j=>w j+y.2)]
  exact (MovingPairedFields.point_translation
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm v k ν χ _ y.1).symm

theorem actual_value_measurable (k:ℕ) (ν χ:ℝ):
    Measurable (fun z:ℝ≥0×(Ω×HeatCircle)=>
      RetainedPairedMovingSection.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm z.1 k ν χ z.2):=by
  convert! value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm ν χ k using 1
  funext z
  exact (value_absolute 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm ν χ z.1 k z.2).symm

end SHE.RetainedPairedMovingFields
