module

public import SHE.HolderResidualScoreInput
public import SHE.FutureResidualScoreInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HolderFutureScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfileStability ControlledProfile MeasurableGaussianScores ControlledResidualScoreInput
local instance : Fact (0<2*π):=⟨by positivity⟩

theorem finite_input_eq_shifted (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (q θ η : ℝ) (old : ControlledProfile.Domain→ℝ)
    {n : ℕ} (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) :
    futureInput σ target center
      (fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p)
      (fun p=>ControlledProfile.profile P Λ u d (θ,p)-ControlledProfile.profile P Λ u d (η,p)) q=
    StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old (q+p.1,p.2))
      (ProfileHolderScoreRates.difference P Λ u d q θ η) := by
  have hpos : ∀ᵐ p : StoppedGaussianFeatures.Domain ∂historyMeasure 0,0<p.1 := by
    have ht : ∀ᵐ r : ℝ ∂volume.restrict (Ici (0:ℝ)),0<r := by
      rw [←Measure.restrict_congr_set (Ioi_ae_eq_Ici : Ioi (0:ℝ)=ᵐ[volume] Ici 0)]
      exact ae_restrict_mem measurableSet_Ioi
    exact Measure.quasiMeasurePreserving_fst.ae ht
  change (fun x : HeatCircle=>∫ p,|ControlledProfile.profile P Λ u d (θ,p)-ControlledProfile.profile P Λ u d (η,p)| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x)
        (fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p) q)
      (stoppedRow σ target (fun i=>center i+x) p) ∂historyMeasure q)=_
  rw [StoppedTimeTranslation.score_input_shift]
  funext x
  apply integral_congr_ae
  filter_upwards [hpos] with p hp
  simp only [StoppedTimeTranslation.shift_apply,ProfileHolderScoreRates.difference,hp,ite_true]

/-- The original full-future covariance score mass of the ACTUAL
finite profile difference has Holder input gain and no earliest-gap
power. Distinct stops, heat targets and the fixed old fraction remain. -/
theorem finite_input (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ) :
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower/2) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1) → (∀ i,σ i≤target i) →
      ∀ hi : ℝ,q<hi → (∀ i,hi≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p
      let e := fun p=>ControlledProfile.profile P Λ u d (θ,p)-ControlledProfile.profile P Λ u d (η,p)
      let F := futureInput σ target center c e q
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        (2*(P.holder*(|θ - η| * ‖d‖)^P.exponent))*(((n:ℝ)/(P.lower/2))*((hi-q)/2)^(0:ℝ)*(1+2/((0:ℝ)+1))) := by
  intro old hold holdb n σ target center hσ1 hages hi hhi hstop c e F
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hages' (i : Fin n) : σ i-q≤target i-q := sub_le_sub_right (hages i) q
  have holdm : Measurable (fun p : ControlledProfile.Domain=>old (q+p.1,p.2)) :=
    hold.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hh := HolderResidualScoreInput.shifted_input P hΛ u d hsmallL2 q hq θ η (fun p=>old (q+p.1,p.2)) holdm
    (fun p=>holdb (q+p.1,p.2)) n (fun i=>σ i-q) (fun i=>target i-q) center
    hσ hσ1 hages' (hi-q) hs (fun i=>sub_le_sub_right (hstop i) q)
  have heq : F=StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old (q+p.1,p.2))
      (ProfileHolderScoreRates.difference P Λ u d q θ η) := by
    exact finite_input_eq_shifted P Λ u d q θ η old σ target center
  simpa only [←heq] using hh

end SHE.HolderFutureScoreInput
