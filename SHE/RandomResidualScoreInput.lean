module

public import SHE.RandomShiftedProfile
public import SHE.ShiftedResidualScoreInput
public import SHE.FutureResidualScoreInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates
open scoped NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- The true sharp score-input estimate for random initial data. One
parameter/sample event works for all current times, residual old profiles,
centers and finite observation lists. -/
theorem random_shifted_input (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ q : ℝ,0≤q →
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower/2) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,0<σ i) → (∀ i,σ i≤1) → (∀ i,σ i≤target i) →
      ∀ s : ℝ,0<s → (∀ i,s≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,(q+p.1,p.2))-old p
      let e := shiftedDerivative P Λ (u ω) (d ω) q θ
      let F := StoppedScoreLeverage.scoreInput σ target center c e
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        sharpConstant P (d ω)*(((n:ℝ)/(P.lower/2))*(s/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1))) := by
  filter_upwards [random_shifted_sharp P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  filter_upwards [hθ] with ω hsharp
  intro q hq old hold holdb n σ target center hσ hσ1 hages s hs hstop c e F
  have hc : Measurable c :=
    ((profile_measurable P Λ (u ω) (d ω)).comp
      (measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk measurable_snd))).sub hold
  have he : Measurable e := shiftedDerivative_measurable P hΛ (u ω) (d ω) hsmallPoint q θ
  have hcb (p : ControlledProfile.Domain) : 0≤c p ∧ c p≤P.upper := by
    have hp := profile_bounds P Λ (u ω) (d ω) (θ,(q+p.1,p.2))
    have ho := holdb p
    dsimp only [c]
    constructor <;> linarith [P.lower_pos]
  have hcl (p : ControlledProfile.Domain) : P.lower/2≤c p := by
    have hp := profile_bounds P Λ (u ω) (d ω) (θ,(q+p.1,p.2))
    have ho := holdb p
    dsimp only [c]
    linarith
  have hcoarse (p : ControlledProfile.Domain) (hp : 0≤p.1) :
      |e p|≤coarseConstant P (d ω)*p.1^((P.exponent-2)/4) :=
    shiftedDerivative_coarse P hΛ (u ω) (d ω) hsmallPoint hq θ p hp
  have hα : -1<(P.exponent-1)/4 := by linarith [P.exponent_pos]
  have hα0 : (P.exponent-1)/4≤0 := by linarith [P.exponent_le_one]
  have hτ : -1<(P.exponent-2)/4 := by linarith [P.exponent_pos]
  have hτ0 : (P.exponent-2)/4<0 := by linarith [P.exponent_le_one]
  have hFm : Measurable F := by
    convert! StoppedCovarianceWordFields.scoreInput_measurable σ target center c e hc he using 1
  have hF0 (x : HeatCircle) : 0≤F x :=
    StoppedScoreLeverage.scoreInput_nonneg σ target center hσ hσ1 hages c hc P.upper (P.lower/2)
      hcb (half_pos P.lower_pos) hcl e x
  have hFb (x : HeatCircle) : F x≤
      coarseConstant P (d ω)*((n:ℝ)/(P.lower/2))*(s/2)^((P.exponent-2)/4)*
        (1+2/(((P.exponent-2)/4)+1)) :=
    (StoppedCovarianceInput.score_input_weighted_bound σ target (fun i=>center i+x)
      hσ hσ1 hages hs hτ hτ0 (coarseConstant_nonneg P (d ω)) hstop c hc P.upper (P.lower/2)
      hcb (half_pos P.lower_pos) hcl e he hcoarse).2
  refine ⟨bounded_memLp hFm (fun x=>by rw [abs_of_nonneg (hF0 x)];exact hFb x),?_⟩
  exact StoppedScoreLeverage.scoreInput_normTwo_bound σ target center hσ hσ1 hages hs hα hα0 hτ hτ0
    (half_pos P.lower_pos) (sharpConstant_nonneg P (d ω)) (coarseConstant_nonneg P (d ω)) hstop
    c hc P.upper hcb hcl e he hcoarse (hsharp q hq) hFm


end SHE.ControlledResidualScoreInput
