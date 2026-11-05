module

public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
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

namespace SHE.MixedPairedCurrentClock
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedPairedCurrentClock_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPairedCurrentClock_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedPairedCurrentClock_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedPairedCurrentClock_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPairedCurrentClock_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedPairedCurrentClock_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPairedCurrentClock_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedPairedCurrentClock_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPairedCurrentClock_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPairedCurrentClock_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPairedCurrentClock_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedPairedCurrentClock_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

def clock (k:ℕ) (t:Fin k→ℝ):ℝ:=
  (carrier Rel k).terminal (MixedPastTerminalSlotSpatial.anchor k t)

theorem clock_measurable (k:ℕ):Measurable (clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k):=
  (carrier Rel k).terminal_measurable.comp
    ((HistoryProductMeasure.separated_measurable k).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))

theorem clock_nonneg (k:ℕ) (t:Fin k→ℝ):0≤clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t:=
  (carrier Rel k).terminal_base _

theorem clock_le (k:ℕ) (t:Fin k→ℝ):clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t≤(h:ℝ):=
  PhysicalScoreChain.terminal_le_initial Rel k _

/-- The TRUE current energy in the absolute remainder is precisely
the original native difference energy at the translated clock. -/
theorem currentEnergy_translation (v:ℝ≥0) (k:ℕ) (t:Fin k→ℝ):
    MixedPastTerminalTimeFields.currentEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm k (fun j=>t j+(v:ℝ))=
    MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      ((v:ℝ)+clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t).toNNReal:=by
  have he:=PairedTimeTranslation.separated_shift (v:=(v:ℝ)) k (0:HeatCircle) t (fun _=>0)
  unfold MixedPastTerminalTimeFields.currentEnergy MixedPastTerminalSlotSpatial.anchor
  rw [←he,ShiftedWordGeometry.terminal_shift Rel (Abs v) (v:ℝ)
    (ControlledWordTimeShift.base_shift P P.coefficient haP Λ h v (0,(0,0)))
    (ControlledWordTimeShift.terminal_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0)))]
  simp only [MixedMovingEnergy.energy,clock,MixedPastTerminalSlotSpatial.anchor,add_comm]

/-- Physical-window zero extension agrees with the actual current
energy on every complete moving reference window. -/
theorem current_power (v:ℝ≥0) (hv:0<v) (hvbH:v+h≤H)
    (k:ℕ) (t:Fin k→ℝ) {χ:ℝ} (hχ:0≤χ):
    ENNReal.ofReal ((MixedPastTerminalTimeFields.currentEnergy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add
        (ZT v) (HT v) (HS v) F hF hFm k (fun j=>t j+(v:ℝ)))^χ)=
    MovingPastFractional.powerWindow (H:ℝ) χ Ee
      ((v:ℝ)+clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t):=by
  let q:=(v:ℝ)+clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t
  have hq:q∈Ioc (0:ℝ) (H:ℝ):=by
    constructor
    · exact add_pos_of_pos_of_nonneg (by exact_mod_cast hv)
        (clock_nonneg (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t)
    · have hh:=clock_le (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) k t
      have hb:(v:ℝ)+(h:ℝ)≤(H:ℝ):=by exact_mod_cast hvbH
      dsimp only [q]
      linarith
  rw [currentEnergy_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm v k t]
  change ENNReal.ofReal ((MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q.toNNReal)^χ)=
    MovingPastFractional.powerWindow (H:ℝ) χ Ee q
  simp only [MovingPastFractional.powerWindow,indicator_of_mem hq,
    MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,indicator_of_mem hq]
  exact (ENNReal.ofReal_rpow_of_nonneg
    (MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S q.toNNReal) hχ).symm

end SHE.MixedPairedCurrentClock

