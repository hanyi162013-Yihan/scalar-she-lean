module

public import SHE.MixedPastTerminalRemainderEnergy
public import SHE.InitialNativeWordFields
public import SHE.MixedTerminalEnergySplit
public import SHE.MixedMovingEnergy
public import SHE.InitialActualConvolution
public import SHE.InitialActualRMSEnvelope
public import SHE.InitialRMSGapEnvelope
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

namespace SHE.InitialNativeClock
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance initialNativeClock_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialNativeClock_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance initialNativeClock_instance3 : MeasurableSpace RealL2 := borel _
local instance initialNativeClock_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance initialNativeClock_instance5 : MeasurableSpace CircleL2 := borel _
local instance initialNativeClock_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance initialNativeClock_instance7 : MeasurableSpace RealHaarInput := borel _
local instance initialNativeClock_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialNativeClock_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialNativeClock_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance initialNativeClock_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance initialNativeClock_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "RT" T:max=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=0) (b:=T) (hvb:=bot_le) (Z:=ZZ T) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
  (F:=F) (hF:=hF) (hFm:=hFm)
local notation "En" T:max=>MixedPastTerminalTimeFields.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 T bot_le (ZZ T)
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- The TRUE initial terminal current has its original newest clock,
including the newest physical zero-age coordinate. -/
theorem current_power (T:ℝ≥0) (hTH:T≤H) (k:ℕ) (t:Fin (k+1)→ℝ)
    (ho:OrderedGapCoordinates.ordered 0 (T:ℝ) (k+1) t) {χ:ℝ} (hχ:0≤χ):
    ENNReal.ofReal (((En T) (k+1) t)^χ)=MovingPastFractional.powerWindow (H:ℝ) χ Ee
      (OrderedGapCoordinates.boundary (T:ℝ) (k+1) t):=by
  let L:=ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 T bot_le (ZZ T)
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,(0,0))
  have hp:=(PhysicalOrderedGaps.strict_active_iff_ordered L (T:ℝ) (fun _=>rfl) 0 le_rfl (k+1) t
    (0:HeatCircle) (fun _=>0)).mpr ho
  have ht:=PhysicalOrderedGaps.terminal_eq_boundary L (T:ℝ) (fun _=>rfl) (k+1) t
    (0:HeatCircle) (fun _=>0) hp.1
  have hq:OrderedGapCoordinates.boundary (T:ℝ) (k+1) t∈Ioc (0:ℝ) (H:ℝ):=by
    have hh:=(PhysicalOrderedGaps.ordered_bounds 0 (T:ℝ) (k+1) t ho).1 0
    exact ⟨hh.1,hh.2.le.trans (by exact_mod_cast hTH)⟩
  have he:(En T) (k+1) t=MixedMovingEnergy.energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      (OrderedGapCoordinates.boundary (T:ℝ) (k+1) t).toNNReal:=by
    unfold MixedPastTerminalTimeFields.currentEnergy MixedMovingEnergy.energy MixedPastTerminalSlotSpatial.anchor
    rw [ht]
  rw [he]
  simp only [MovingPastFractional.powerWindow,indicator_of_mem hq,MixedMovingEnergy.ennEnergy,
    MixedMovingEnergy.realEnergy,indicator_of_mem hq]
  exact (ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun _=>sq_nonneg _)) hχ).symm

/-- Multiplying by the ACTUAL RMS support gives an exact initial-clock
identity globally, including every inactive ordering configuration. -/
theorem rms_current_product (T:ℝ≥0) (hTH:T≤H) (k:ℕ) (t:Fin (k+1)→ℝ)
    (χ A0 ν:ℝ) (hχ:0≤χ) (order:ℕ) (B0:ℝ≥0):
    ENNReal.ofReal ((RT T) (k+1) t ν χ A0 order B0)*ENNReal.ofReal (((En T) (k+1) t)^χ)=
      ENNReal.ofReal ((RT T) (k+1) t ν χ A0 order B0)*
        MovingPastFractional.powerWindow (H:ℝ) χ Ee (OrderedGapCoordinates.boundary (T:ℝ) (k+1) t):=by
  by_cases ho:OrderedGapCoordinates.ordered 0 (T:ℝ) (k+1) t
  · rw [current_power 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm T hTH k t ho hχ]
  · let L:=ControlledReferenceThetaGeometry.level P P.coefficient haP Λ 0 T bot_le (ZZ T)
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,(0,0))
    have hn:¬PhysicalParentGeometry.StrictHistory L (k+1) (MixedPastTerminalSlotSpatial.anchor (k+1) t):=by
      intro hp
      have ha:=(ControlledTerminalPairedTime.strict_active P haP Λ 0 T bot_le (ZZ T)
        (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k t).mpr hp
      exact ho ((PhysicalOrderedGaps.strict_active_iff_ordered L (T:ℝ) (fun _=>rfl) 0 le_rfl (k+1) t
        (0:HeatCircle) (fun _=>0)).mp ha)
    dsimp only [L] at hn
    simp only [MixedPastTerminalRMS.amplitude,ControlledTerminalPairedTime.amplitude,if_neg hn,
      mul_zero,Finset.sum_const_zero,ENNReal.ofReal_zero,zero_mul]

end SHE.InitialNativeClock
