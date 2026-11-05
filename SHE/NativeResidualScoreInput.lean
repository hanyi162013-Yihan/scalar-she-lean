module
public import SHE.RandomFutureInputEnergy
public import SHE.RandomShiftedProfile
public import SHE.NativeFirstScoreReserve
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.NativeResidualScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates ControlledResidualScoreInput
open scoped NNReal
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {W:Type*}[MeasurableSpace W][MeasurableSpace CircleL2][BorelSpace CircleL2]

/-- Actual sharp signed profile-input bound with the genuine three-eighths
fresh floor after the native first-score reserve has been removed. The
old profile may consume five eighths; no half-floor assumption is used. -/
theorem random_shifted_input (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ q : ℝ,0≤q →
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤5*P.lower/8) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,0<σ i) → (∀ i,σ i≤1) → (∀ i,σ i≤target i) →
      ∀ s : ℝ,0<s → (∀ i,s≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,(q+p.1,p.2))-old p
      let e := shiftedDerivative P Λ (u ω) (d ω) q θ
      let F := StoppedScoreLeverage.scoreInput σ target center c e
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        sharpConstant P (d ω)*(((n:ℝ)/(3*P.lower/8))*(s/2)^((P.exponent-1)/4)*
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
  have hcl (p : ControlledProfile.Domain) : 3*P.lower/8≤c p := by
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
    StoppedScoreLeverage.scoreInput_nonneg σ target center hσ hσ1 hages c hc P.upper (3*P.lower/8)
      hcb (by have :=P.lower_pos; positivity : 0<3*P.lower/8) hcl e x
  have hFb (x : HeatCircle) : F x≤
      coarseConstant P (d ω)*((n:ℝ)/(3*P.lower/8))*(s/2)^((P.exponent-2)/4)*
        (1+2/(((P.exponent-2)/4)+1)) :=
    (StoppedCovarianceInput.score_input_weighted_bound σ target (fun i=>center i+x)
      hσ hσ1 hages hs hτ hτ0 (coarseConstant_nonneg P (d ω)) hstop c hc P.upper (3*P.lower/8)
      hcb (by have :=P.lower_pos; positivity : 0<3*P.lower/8) hcl e he hcoarse).2
  refine ⟨bounded_memLp hFm (fun x=>by rw [abs_of_nonneg (hF0 x)];exact hFb x),?_⟩
  exact StoppedScoreLeverage.scoreInput_normTwo_bound σ target center hσ hσ1 hages hs hα hα0 hτ hτ0
    (by have :=P.lower_pos; positivity : 0<3*P.lower/8) (sharpConstant_nonneg P (d ω)) (coarseConstant_nonneg P (d ω)) hstop
    c hc P.upper hcb hcl e he hcoarse (hsharp q hq) hFm



/-- The original future clock and all stop masks are retained. -/
theorem random_future_input (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ q : ℝ,0≤q →
      ∀ (old : ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤5*P.lower/8) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1) → (∀ i,σ i≤target i) →
      ∀ hi : ℝ,q<hi → (∀ i,hi≤σ i) →
      let c := fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,p)-old p
      let e := fun p=>ControlledProfile.derivative P Λ (u ω) (d ω) (p,θ)
      let F := futureInput σ target center c e q
      MemLp F 2 haarAddCircle ∧ normTwo haarAddCircle F≤
        sharpConstant P (d ω)*(((n:ℝ)/(3*P.lower/8))*((hi-q)/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1))) := by
  filter_upwards [random_shifted_input P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  filter_upwards [hθ] with ω hω
  intro q hq old hold holdb n σ target center hσ1 hages hi hhi hstop c e F
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hages' (i : Fin n) : σ i-q≤target i-q := sub_le_sub_right (hages i) q
  have holdm : Measurable (fun p : ControlledProfile.Domain=>old (q+p.1,p.2)) :=
    hold.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hh := hω q hq (fun p=>old (q+p.1,p.2)) holdm
    (fun p=>holdb (q+p.1,p.2)) n (fun i=>σ i-q) (fun i=>target i-q) center
    hσ hσ1 hages' (hi-q) hs (fun i=>sub_le_sub_right (hstop i) q)
  have heq : F=StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>ControlledProfile.profile P Λ (u ω) (d ω) (θ,(q+p.1,p.2))-old (q+p.1,p.2))
      (shiftedDerivative P Λ (u ω) (d ω) q θ) := by
    exact futureInput_eq_shifted P Λ (u ω) (d ω) q θ old σ target center
  simpa only [←heq] using hh



/-- Actual correlated sample/output energy of the native residual input. -/
theorem random_future_energy (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ) :
    ∀ᵐ θ ∂volume,∀ q : ℝ,0≤q →
      ∀ (old : W×ControlledProfile.Domain→ℝ),Measurable old →
      (∀ p,0≤old p ∧ old p≤5*P.lower/8) →
      ∀ (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i-q≤1) → (∀ i,σ i≤target i) →
      ∀ hi : ℝ,q<hi → (∀ i,hi≤σ i) →
      let c := fun z : W×ControlledProfile.Domain=>profile P Λ (u z.1) (d z.1) (θ,z.2)-old z
      let e := fun z : W×ControlledProfile.Domain=>derivative P Λ (u z.1) (d z.1) (z.2,θ)
      let F := fun z : W×HeatCircle=>futureInput σ target center
        (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
      let C := sharpUnit P*(((n:ℝ)/(3*P.lower/8))*((hi-q)/2)^((P.exponent-1)/4)*
        (1+2/(((P.exponent-1)/4)+1)))
      Integrable (fun z=>|F z|^2) (μ.prod haarAddCircle) ∧
        (∫ z,|F z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ ω,‖d ω‖^2 ∂μ) := by
  filter_upwards [random_future_input P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  intro q hq old hold holdb n σ target center hσ1 hages hi hhi hstop c e F C
  have hc : Measurable c := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>((z.1,θ),z.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    have hh := (random_profile_measurable P hu hd Λ).comp hmap
    convert! hh.sub hold using 1
  have he : Measurable e := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>(z,θ)) :=
      measurable_id.prodMk measurable_const
    convert! (random_derivative_measurable P hΛ u d hu hd hsmallPoint).comp
      hmap using 1
  have hFm : Measurable F := futureInput_random_measurable σ target center c e hc he q
  have hBi : Integrable (fun ω=>C^2*‖d ω‖^2) μ := hdi.const_mul _
  have hh : ∀ᵐ ω ∂μ,Integrable (fun x : HeatCircle=>‖F (ω,x)‖^2) haarAddCircle ∧
      (∫ x : HeatCircle,‖F (ω,x)‖^2 ∂haarAddCircle)≤C^2*‖d ω‖^2 := by
    filter_upwards [hθ] with ω hω
    have ho : Measurable (fun p=>old (ω,p)) := hold.comp (measurable_const.prodMk measurable_id)
    have hp := hω q hq (fun p=>old (ω,p)) ho (fun p=>holdb (ω,p))
      n σ target center hσ1 hages hi hhi hstop
    refine ⟨hp.1.norm.integrable_sq,?_⟩
    have hpow := pow_le_pow_left₀ (normTwo_nonneg haarAddCircle _) hp.2 2
    rw [normTwo_sq] at hpow
    simpa only [F,c,e,C,sharpConstant_factor,mul_pow,mul_assoc,mul_comm,mul_left_comm,
      Real.norm_eq_abs,sq_abs] using hpow
  have hb := SectionEnergy.product_energy haarAddCircle μ F hFm
    (fun ω=>C^2*‖d ω‖^2) hBi (hh.mono (fun _ h=>h.1)) (hh.mono (fun _ h=>h.2))
  refine ⟨by simpa only [Real.norm_eq_abs] using hb.1,?_⟩
  simpa only [Real.norm_eq_abs,integral_const_mul] using hb.2


end SHE.NativeResidualScoreInput
