module

public import SHE.RandomPastAgeProfile
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
local instance pastAgeResidualScoreInput_period : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- The original past age controls the profile derivative throughout the
future history. The leverage estimate uses temporal exponent ZERO, so
this sharper bound has no inverse power of the remaining fresh gap.
A single theta/sample event works for all positive past ages and floors. -/
theorem random_past_age_shifted_input (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ q : ℝ,0<q →
      ∀ ell : ℝ,0<ell →
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤P.lower-ell) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,0<σ i) → (∀ i,σ i≤1) → (∀ i,σ i≤target i) →
      ∀ s : ℝ,0<s → (∀ i,s≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,(q+p.1,p.2))-old p
      let e := shiftedDerivative P Λ (u ω) (d ω) q θ
      let F := StoppedScoreLeverage.scoreInput σ target center c e
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        (sharpConstant P (d ω)*q^((P.exponent-1)/4))*(((n:ℝ)/ell)*3) := by
  filter_upwards [random_past_age_sharp P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  filter_upwards [hθ] with ω hsharp
  intro q hq ell hell old hold holdb n σ target center hσ hσ1 hages s hs hstop c e F
  have hc : Measurable c :=
    ((profile_measurable P Λ (u ω) (d ω)).comp
      (measurable_const.prodMk ((measurable_const.add measurable_fst).prodMk measurable_snd))).sub hold
  have he : Measurable e := shiftedDerivative_measurable P hΛ (u ω) (d ω) hsmallPoint q θ
  have hcb (p : ControlledProfile.Domain) : 0≤c p ∧ c p≤P.upper := by
    have hp := profile_bounds P Λ (u ω) (d ω) (θ,(q+p.1,p.2))
    have ho := holdb p
    dsimp only [c]
    constructor <;> linarith [P.lower_pos,hell]
  have hcl (p : ControlledProfile.Domain) : ell≤c p := by
    have hp := profile_bounds P Λ (u ω) (d ω) (θ,(q+p.1,p.2))
    have ho := holdb p
    dsimp only [c]
    linarith
  have hcoarse (p : ControlledProfile.Domain) (hp : 0≤p.1) :
      |e p|≤coarseConstant P (d ω)*p.1^((P.exponent-2)/4) :=
    shiftedDerivative_coarse P hΛ (u ω) (d ω) hsmallPoint hq.le θ p hp
  have hα : -1<(P.exponent-1)/4 := by linarith [P.exponent_pos]
  have hα0 : (P.exponent-1)/4≤0 := by linarith [P.exponent_le_one]
  have hτ : -1<(P.exponent-2)/4 := by linarith [P.exponent_pos]
  have hτ0 : (P.exponent-2)/4<0 := by linarith [P.exponent_le_one]
  have hFm : Measurable F := by
    convert! StoppedCovarianceWordFields.scoreInput_measurable σ target center c e hc he using 1
  have hF0 (x : HeatCircle) : 0≤F x :=
    StoppedScoreLeverage.scoreInput_nonneg σ target center hσ hσ1 hages c hc P.upper (ell)
      hcb hell hcl e x
  have hFb (x : HeatCircle) : F x≤
      coarseConstant P (d ω)*((n:ℝ)/(ell))*(s/2)^((P.exponent-2)/4)*
        (1+2/(((P.exponent-2)/4)+1)) :=
    (StoppedCovarianceInput.score_input_weighted_bound σ target (fun i=>center i+x)
      hσ hσ1 hages hs hτ hτ0 (coarseConstant_nonneg P (d ω)) hstop c hc P.upper (ell)
      hcb hell hcl e he hcoarse).2
  refine ⟨bounded_memLp hFm (fun x=>by rw [abs_of_nonneg (hF0 x)];exact hFb x),?_⟩
  have hsharp0 : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),
      normTwo haarAddCircle (fun x=>e (r,x))≤
        (sharpConstant P (d ω)*q^((P.exponent-1)/4))*r^(0:ℝ) := by
    simpa only [rpow_zero,mul_one] using hsharp q hq
  have hh:=StoppedScoreLeverage.scoreInput_normTwo_bound σ target center hσ hσ1 hages hs
    (show (-1:ℝ)<0 by norm_num) (le_refl (0:ℝ)) hτ hτ0
    hell (mul_nonneg (sharpConstant_nonneg P (d ω)) (rpow_nonneg hq.le _))
    (coarseConstant_nonneg P (d ω)) hstop
    c hc P.upper hcb hcl e he hcoarse hsharp0 hFm
  norm_num only [rpow_zero,mul_one,zero_add,div_one,show (1:ℝ)+2=3 by norm_num] at hh
  exact hh


end SHE.ControlledResidualScoreInput
