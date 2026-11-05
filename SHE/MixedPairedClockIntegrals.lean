module

public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
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

namespace SHE.MixedPairedClockIntegrals
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedPairedClockIntegrals_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPairedClockIntegrals_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedPairedClockIntegrals_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedPairedClockIntegrals_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPairedClockIntegrals_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedPairedClockIntegrals_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPairedClockIntegrals_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedPairedClockIntegrals_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPairedClockIntegrals_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPairedClockIntegrals_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPairedClockIntegrals_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedPairedClockIntegrals_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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
local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm (0,(0,0))
local notation "RMS"=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=0) (b:=h) (hvb:=bot_le) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)

local notation "Abs" v=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v

local notation "RAbs" v=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=v) (b:=v+h) (hvb:=le_self_add) (Z:=ZT v) (htarget:=HT v) (hstop:=HS v) (F:=F) (hF:=hF) (hFm:=hFm)
local notation "EAbs" v=>MixedPastTerminalTimeFields.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "Clock"=>MixedPairedCurrentClock.clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h)
  (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)

theorem pi_translation (v:ℝ≥0) (k:ℕ):
    MeasurePreserving (fun t:Fin k→ℝ=>fun j=>t j+(v:ℝ))
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (0:ℝ) (h:ℝ))))
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ)))):=by
  simpa only [zero_add,NNReal.coe_add,add_comm (h:ℝ) (v:ℝ)] using
    PairedTimeTranslation.pi_translation (v:=(v:ℝ)) 0 (h:ℝ) k

/-- Exact original-volume RMS mass translation. -/
theorem mass_translation (v:ℝ≥0) (k:ℕ) (χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0):
    (∫t,(RAbs v) k t ν χ A0 order B0
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))))=
    ∫t,RMS k t ν χ A0 order B0 ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (0:ℝ) (h:ℝ))):=by
  have he:MeasurableEmbedding (fun t:Fin k→ℝ=>fun j=>t j+(v:ℝ)):=
    (Homeomorph.addRight (fun _:Fin k=>(v:ℝ))).measurableEmbedding
  rw [←(pi_translation (h:=h) v k).integral_comp he (fun t=>(RAbs v) k t ν χ A0 order B0)]
  simp_rw [ControlledPairedTimeTranslation.rms_translation P haP Λ h Z htarget hstop F hF hFm κ M v k]

/-- The current factor is the TRUE native difference energy at the
translated relative terminal, with no law or covariance replacement. -/
theorem energy_translation (v:ℝ≥0) (k:ℕ) (χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0):
    (∫t,(RAbs v) k t ν χ A0 order B0*((EAbs v) k t)^χ
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))))=
    ∫t,RMS k t ν χ A0 order B0*
      (MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        ((v:ℝ)+Clock k t).toNNReal)^χ
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc (0:ℝ) (h:ℝ))):=by
  have he:MeasurableEmbedding (fun t:Fin k→ℝ=>fun j=>t j+(v:ℝ)):=
    (Homeomorph.addRight (fun _:Fin k=>(v:ℝ))).measurableEmbedding
  rw [←(pi_translation (h:=h) v k).integral_comp he
    (fun t=>(RAbs v) k t ν χ A0 order B0*((EAbs v) k t)^χ)]
  simp_rw [ControlledPairedTimeTranslation.rms_translation P haP Λ h Z htarget hstop F hF hFm κ M v k,
    MixedPairedCurrentClock.currentEnergy_translation
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm v k]

end SHE.MixedPairedClockIntegrals

