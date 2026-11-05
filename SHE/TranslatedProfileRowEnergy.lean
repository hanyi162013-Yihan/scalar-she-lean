module

public import SHE.StoppedCovarianceInput
public import SHE.RelativeHistoryGeometry
public import SHE.ObservationTimeShift
public import SHE.ControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.TranslatedProfileRowEnergy
open Set MeasureTheory StoppedGaussianFeatures StoppedFourier
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain CoveredControlledLaw
local instance translatedProfileRowEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- Absolute-time physical row energy follows by an exact translation of
the integrable relative-time profile bound. No score range assertion is
needed for this coarse applicability statement. -/
theorem translated_integrable (v q : ℝ) (hq : v≤q)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i-v) (hσ1 : ∀ i,σ i-v≤1)
    (hages : ∀ i,σ i≤target i) (e : Domain→ℝ) (he : Measurable e)
    {E τ : ℝ} (hτ : -1<τ) (hdom : ∀ p,0≤p.1→|e p|≤E*p.1^τ) :
    Integrable (fun p=>|ObservationTimeShift.profile v e p| * ‖stoppedRow σ target center p‖^2)
      (historyMeasure q) := by
  have hi:=StoppedCovarianceInput.weighted_input_energy_integrable
    (fun i=>σ i-v) (fun i=>target i-v) center hσ hσ1
    (fun i=>sub_le_sub_right (hages i) v) e he hτ hdom
  have hir:=hi.mono_measure (StoppedRowWeighted.historyMeasure_mono (sub_nonneg.mpr hq))
  have hm:=ObservationTimeShift.history_translation v (q-v)
  rw [sub_add_cancel] at hm
  apply (hm.integrable_comp_emb (ObservationTimeShift.translation v).measurableEmbedding).mp
  convert! hir using 1
  funext p
  change |ObservationTimeShift.profile v e (ObservationTimeShift.translation v p)| *
    ‖stoppedRow σ target center (ObservationTimeShift.translation v p)‖^2=_
  rw [ObservationTimeShift.profile_translation]
  have hh:=ObservationTimeShift.stoppedRow_translation v (fun i=>σ i-v) (fun i=>target i-v) center p
  simpa only [sub_add_cancel] using congrArg (fun z=>|e p| * ‖z‖^2) hh

/-- The literal controlled profile derivative has finite absolute
physical frame energy after translation from an arbitrary past. -/
theorem controlled_integrable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0≤Λ)
    (u d : CircleL2)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ v q : ℝ) (hq : v≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i-v) (hσ1 : ∀ i,σ i-v≤1) (hages : ∀ i,σ i≤target i) :
    Integrable (fun p=>|ObservationTimeShift.profile v
      (fun z=>ControlledProfile.derivative P Λ u d (z,θ)) p| * ‖stoppedRow σ target center p‖^2)
      (historyMeasure q) := by
  apply translated_integrable v q hq σ target center hσ hσ1 hages _
    ((ControlledProfile.derivative_measurable P hΛ u d hsmall).comp (measurable_id.prodMk measurable_const))
    (E:=ControlledScoreRates.coarseConstant P d) (τ:=(P.exponent-2)/4)
  · linarith [P.exponent_pos]
  · exact ControlledScoreRates.derivative_coarse_power P hΛ u d hsmall θ

end SHE.TranslatedProfileRowEnergy
