module

public import SHE.FutureInputCoarse

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
local instance : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

/-- The literal original future score integrand is genuinely Bochner
integrable for EVERY parameter and output point. Its coarse rate is used
only for applicability; the quantitative energy uses the sharp L2 rate. -/
theorem future_input_integrable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ q : ℝ) (hq : 0≤q) (old : ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (holdb : ∀ p,0≤old p ∧ old p≤P.lower/2)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i) (x : HeatCircle) :
    Integrable (fun p=>|ControlledProfile.derivative P Λ u d (p,θ)| *MeasurableGaussianScores.scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target (fun i=>center i+x)
        (fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p) q)
      (StoppedGaussianFeatures.stoppedRow σ target (fun i=>center i+x) p))
        (StoppedGaussianFeatures.historyMeasure q) := by
  let c' : ControlledProfile.Domain→ℝ := fun p=>
    ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old (q+p.1,p.2)
  let e' := shiftedDerivative P Λ u d q θ
  have hc' : Measurable c' :=
    ((profile_measurable P Λ u d).comp
      (measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk measurable_snd))).sub
        (hold.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
  have he' : Measurable e' := shiftedDerivative_measurable P hΛ u d hsmallPoint q θ
  have hcb (p : ControlledProfile.Domain) : 0≤c' p ∧ c' p≤P.upper := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb (q+p.1,p.2)
    dsimp only [c']
    constructor <;> linarith [P.lower_pos]
  have hcl (p : ControlledProfile.Domain) : P.lower/2≤c' p := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb (q+p.1,p.2)
    dsimp only [c']
    linarith
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hτ : -1<(P.exponent-2)/4 := by linarith [P.exponent_pos]
  have hτ0 : (P.exponent-2)/4<0 := by linarith [P.exponent_le_one]
  have hrel := (StoppedCovarianceInput.score_input_weighted_bound
    (fun i=>σ i-q) (fun i=>target i-q) (fun i=>center i+x) hσ hσ1
    (fun i=>sub_le_sub_right (hages i) q) hs hτ hτ0 (coarseConstant_nonneg P d)
    (fun i=>sub_le_sub_right (hstop i) q) c' hc' P.upper (P.lower/2) hcb
    (half_pos P.lower_pos) hcl e' he'
    (fun p hp=>shiftedDerivative_coarse P hΛ u d hsmallPoint hq θ p hp)).1
  apply ((StoppedTimeTranslation.shift_preserving q).integrable_comp_emb
    (StoppedTimeTranslation.shift q).measurableEmbedding).mp
  apply hrel.congr
  have hpos : ∀ᵐ p : StoppedGaussianFeatures.Domain ∂StoppedGaussianFeatures.historyMeasure 0,0<p.1 := by
    have ht : ∀ᵐ r : ℝ ∂volume.restrict (Ici (0:ℝ)),0<r := by
      rw [←Measure.restrict_congr_set (Ioi_ae_eq_Ici : Ioi (0:ℝ)=ᵐ[volume] Ici 0)]
      exact ae_restrict_mem measurableSet_Ioi
    exact Measure.quasiMeasurePreserving_fst.ae ht
  filter_upwards [hpos] with p hp
  dsimp only [Function.comp_def]
  conv_rhs => rw [StoppedTimeTranslation.covariance_shift]
  rw [StoppedTimeTranslation.row_shift]
  simp only [c',e',shiftedDerivative,hp,ite_true,StoppedTimeTranslation.shift_apply]

end SHE.ControlledResidualScoreInput
