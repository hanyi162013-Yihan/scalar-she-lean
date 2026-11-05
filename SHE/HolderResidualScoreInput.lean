module

public import SHE.ProfileHolderScoreRates
public import SHE.ControlledResidualScoreInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HolderResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfileStability ControlledProfile MeasurableGaussianScores
local instance : Fact (0<2*π):=⟨by positivity⟩

/-- The actual finite controlled-profile covariance source has a true
spatial L2 score-mass bound with sharp temporal weight zero. No theta
exception or lower-gap loss is introduced into the Holder source. -/
theorem shifted_input (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ) :
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower/2) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,0<σ i) → (∀ i,σ i≤1) → (∀ i,σ i≤target i) →
      ∀ s : ℝ,0<s → (∀ i,s≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ u d (θ,(q+p.1,p.2))-old p
      let e := ProfileHolderScoreRates.difference P Λ u d q θ η
      let F := StoppedScoreLeverage.scoreInput σ target center c e
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        (2*(P.holder*(|θ - η| * ‖d‖)^P.exponent))*(((n:ℝ)/(P.lower/2))*(s/2)^(0:ℝ)*(1+2/((0:ℝ)+1))) := by
  intro old hold holdb n σ target center hσ hσ1 hages s hs hstop c e F
  have hc : Measurable c :=
    ((profile_measurable P Λ u d).comp
      (measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk measurable_snd))).sub hold
  have he : Measurable e := ProfileHolderScoreRates.difference_measurable P Λ u d q θ η
  have hcb (p : ControlledProfile.Domain) : 0≤c p ∧ c p≤P.upper := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb p
    dsimp only [c]
    constructor <;> linarith [P.lower_pos]
  have hcl (p : ControlledProfile.Domain) : P.lower/2≤c p := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb p
    dsimp only [c]
    linarith
  have hcoarse (p : ControlledProfile.Domain) (hp : 0≤p.1) :
      |e p|≤(2*P.upper)*p.1^(-(1/4:ℝ)) :=
    ProfileHolderScoreRates.difference_coarse P Λ u d hq θ η p hp
  have hα : -1<(0:ℝ) := by linarith [P.exponent_pos]
  have hα0 : (0:ℝ)≤0 := by linarith [P.exponent_le_one]
  have hτ : -1 < -(1/4:ℝ) := by norm_num
  have hτ0 : -(1/4:ℝ)<0 := by linarith [P.exponent_le_one]
  have hFm : Measurable F := by
    convert! StoppedCovarianceWordFields.scoreInput_measurable σ target center c e hc he using 1
  have hF0 (x : HeatCircle) : 0≤F x :=
    StoppedScoreLeverage.scoreInput_nonneg σ target center hσ hσ1 hages c hc P.upper (P.lower/2)
      hcb (half_pos P.lower_pos) hcl e x
  have hFb (x : HeatCircle) : F x≤
      (2*P.upper)*((n:ℝ)/(P.lower/2))*(s/2)^(-(1/4:ℝ))*
        (1+2/((-(1/4:ℝ))+1)) :=
    (StoppedCovarianceInput.score_input_weighted_bound σ target (fun i=>center i+x)
      hσ hσ1 hages hs hτ hτ0 ((mul_nonneg (by norm_num) P.upper_nonneg)) hstop c hc P.upper (P.lower/2)
      hcb (half_pos P.lower_pos) hcl e he hcoarse).2
  refine ⟨bounded_memLp hFm (fun x=>by rw [abs_of_nonneg (hF0 x)];exact hFb x),?_⟩
  exact StoppedScoreLeverage.scoreInput_normTwo_bound σ target center hσ hσ1 hages hs hα hα0 hτ hτ0
    (half_pos P.lower_pos) (mul_nonneg (by norm_num) (mul_nonneg P.holder_nonneg (rpow_nonneg (by positivity) _))) ((mul_nonneg (by norm_num) P.upper_nonneg)) hstop
    c hc P.upper hcb hcl e he hcoarse ((ae_of_all _ (fun r=>by simpa only [rpow_zero,mul_one] using ProfileHolderScoreRates.difference_sharp P hΛ u d hsmallL2 q θ η r))) hFm

end SHE.HolderResidualScoreInput
