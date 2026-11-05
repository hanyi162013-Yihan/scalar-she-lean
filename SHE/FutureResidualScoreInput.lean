module

public import SHE.ShiftedResidualScoreInput
public import SHE.StoppedTimeTranslation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
  MeasurableGaussianScores
open scoped NNReal
local instance futureResidualScoreInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩

def futureInput {n : ℕ} (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (c e : StoppedGaussianFeatures.Domain→ℝ) (q : ℝ) (x : HeatCircle) : ℝ :=
  ∫ p,|e p| *scoreVariance (stoppedCovariance σ target (fun i=>center i+x) c q)
    (stoppedRow σ target (fun i=>center i+x) p) ∂historyMeasure q

theorem futureInput_eq_shifted (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (q θ : ℝ) (old : ControlledProfile.Domain→ℝ)
    {n : ℕ} (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) :
    futureInput σ target center
      (fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p)
      (fun p=>ControlledProfile.derivative P Λ u d (p,θ)) q=
    StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old (q+p.1,p.2))
      (shiftedDerivative P Λ u d q θ) := by
  have hpos : ∀ᵐ p : StoppedGaussianFeatures.Domain ∂historyMeasure 0,0<p.1 := by
    have ht : ∀ᵐ r : ℝ ∂volume.restrict (Ici (0:ℝ)),0<r := by
      rw [←Measure.restrict_congr_set (Ioi_ae_eq_Ici : Ioi (0:ℝ)=ᵐ[volume] Ici 0)]
      exact ae_restrict_mem measurableSet_Ioi
    exact Measure.quasiMeasurePreserving_fst.ae ht
  change (fun x : HeatCircle=>∫ p,|ControlledProfile.derivative P Λ u d (p,θ)| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x)
        (fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p) q)
      (stoppedRow σ target (fun i=>center i+x) p) ∂historyMeasure q)=_
  rw [StoppedTimeTranslation.score_input_shift]
  funext x
  apply integral_congr_ae
  filter_upwards [hpos] with p hp
  simp only [StoppedTimeTranslation.shift_apply,shiftedDerivative,hp,ite_true]

/-- The literal absolute-time full-future score input has the sharp
spatial rate in its remaining earliest gap. All distinct stop masks and
targets survive the exact time translation. -/
theorem future_residual_one_input (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2) :
    ∀ᵐ θ ∂volume,∀ q : ℝ,0≤q →
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower/2) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1) → (∀ i,σ i≤target i) →
      ∀ hi : ℝ,q<hi → (∀ i,hi≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p
      let e := fun p=>ControlledProfile.derivative P Λ u d (p,θ)
      let F := futureInput σ target center c e q
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        sharpConstant P d*(((n:ℝ)/(P.lower/2))*((hi-q)/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1))) := by
  filter_upwards [shifted_residual_one_input P hΛ u d hsmallPoint hsmallL2] with θ hθ
  intro q hq old hold holdb n σ target center hσ1 hages hi hhi hstop c e F
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hages' (i : Fin n) : σ i-q≤target i-q := sub_le_sub_right (hages i) q
  have holdm : Measurable (fun p : ControlledProfile.Domain=>old (q+p.1,p.2)) :=
    hold.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hh := hθ q hq (fun p=>old (q+p.1,p.2)) holdm
    (fun p=>holdb (q+p.1,p.2)) n (fun i=>σ i-q) (fun i=>target i-q) center
    hσ hσ1 hages' (hi-q) hs (fun i=>sub_le_sub_right (hstop i) q)
  have heq : F=StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old (q+p.1,p.2))
      (shiftedDerivative P Λ u d q θ) := by
    exact futureInput_eq_shifted P Λ u d q θ old σ target center
  simpa only [←heq] using hh

end SHE.ControlledResidualScoreInput
