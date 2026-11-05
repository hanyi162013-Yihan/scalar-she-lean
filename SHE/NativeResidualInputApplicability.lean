module
public import SHE.NativeResidualScoreInput
public import SHE.FutureInputIntegrable
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeResidualInputApplicability
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates ControlledResidualScoreInput
open scoped NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- A finite point bound for the literal remaining covariance input.
It is used only for spatial Fubini; the quantitative comparison keeps
the sharper spatial L2 bound. All original stopping masks are retained. -/
theorem future_input_coarse (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ q : ℝ) (hq : 0≤q) (old : ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (holdb : ∀ p,0≤old p ∧ old p≤5*P.lower/8)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i) (x : HeatCircle) :
    let c := fun p=>ControlledProfile.profile P Λ u d (θ,p)-old p
    let e := fun p=>ControlledProfile.derivative P Λ u d (p,θ)
    0≤futureInput σ target center c e q x ∧
    futureInput σ target center c e q x≤
      coarseConstant P d*((n:ℝ)/(3*P.lower/8))*((hi-q)/2)^((P.exponent-2)/4)*
        (1+2/(((P.exponent-2)/4)+1)) := by
  dsimp only
  rw [futureInput_eq_shifted]
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
  have hcl (p : ControlledProfile.Domain) : 3*P.lower/8≤c' p := by
    have hp := profile_bounds P Λ u d (θ,(q+p.1,p.2))
    have ho := holdb (q+p.1,p.2)
    dsimp only [c']
    linarith
  have hs : 0<hi-q := sub_pos.mpr hhi
  have hσ (i : Fin n) : 0<σ i-q := lt_of_lt_of_le hs (sub_le_sub_right (hstop i) q)
  have hτ : -1<(P.exponent-2)/4 := by linarith [P.exponent_pos]
  have hτ0 : (P.exponent-2)/4<0 := by linarith [P.exponent_le_one]
  refine ⟨StoppedScoreLeverage.scoreInput_nonneg _ _ _ hσ hσ1
    (fun i=>sub_le_sub_right (hages i) q) c' hc' P.upper (3*P.lower/8) hcb
      (by have := P.lower_pos; positivity : 0<3*P.lower/8) hcl e' x,?_⟩
  exact (StoppedCovarianceInput.score_input_weighted_bound
    (fun i=>σ i-q) (fun i=>target i-q) (fun i=>center i+x) hσ hσ1
    (fun i=>sub_le_sub_right (hages i) q) hs hτ hτ0 (coarseConstant_nonneg P d)
    (fun i=>sub_le_sub_right (hstop i) q) c' hc' P.upper (3*P.lower/8) hcb
    (by have := P.lower_pos; positivity : 0<3*P.lower/8) hcl e' he'
    (fun p hp=>shiftedDerivative_coarse P hΛ u d hsmallPoint hq θ p hp)).2


/-- The literal original future score integrand is genuinely Bochner
integrable for EVERY parameter and output point. Its coarse rate is used
only for applicability; the quantitative energy uses the sharp L2 rate. -/
theorem future_input_integrable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (θ q : ℝ) (hq : 0≤q) (old : ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (holdb : ∀ p,0≤old p ∧ old p≤5*P.lower/8)
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
  have hcl (p : ControlledProfile.Domain) : 3*P.lower/8≤c' p := by
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
    (fun i=>sub_le_sub_right (hstop i) q) c' hc' P.upper (3*P.lower/8) hcb
    (by have := P.lower_pos; positivity : 0<3*P.lower/8) hcl e' he'
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


/-- Coarse bounds prove the true random mass square is integrable at
EVERY fixed output point and parameter. This is an applicability result;
the quantitative covariance estimate uses the sharper product energy. -/
theorem random_future_point_integrable (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ)
    (θ q : ℝ) (hq : 0≤q) (old : W×ControlledProfile.Domain→ℝ) (hold : Measurable old)
    (holdb : ∀ p,0≤old p ∧ old p≤5*P.lower/8)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (hi : ℝ) (hhi : q<hi) (hstop : ∀ i,hi≤σ i) (x : HeatCircle) :
    let c := fun z : W×ControlledProfile.Domain=>profile P Λ (u z.1) (d z.1) (θ,z.2)-old z
    let e := fun z : W×ControlledProfile.Domain=>derivative P Λ (u z.1) (d z.1) (z.2,θ)
    Integrable (fun ω=>(futureInput σ target center (fun p=>c (ω,p)) (fun p=>e (ω,p)) q x)^2) μ := by
  intro c e
  let G : W→ℝ := fun ω=>futureInput σ target center (fun p=>c (ω,p)) (fun p=>e (ω,p)) q x
  let K : ℝ := 2*(meanConstant P.lower P.holder P.exponent*sqrt (1+heatConstant))*
    ((n:ℝ)/(3*P.lower/8))*((hi-q)/2)^((P.exponent-2)/4)*(1+2/(((P.exponent-2)/4)+1))
  have hc : Measurable c := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>((z.1,θ),z.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk measurable_snd
    convert! ((random_profile_measurable P hu hd Λ).comp hmap).sub hold using 1
  have he : Measurable e := by
    have hmap : Measurable (fun z : W×ControlledProfile.Domain=>(z,θ)) :=
      measurable_id.prodMk measurable_const
    convert! (random_derivative_measurable P hΛ u d hu hd hsmallPoint).comp hmap using 1
  have hm : Measurable G := by
    convert! (futureInput_random_measurable σ target center c e hc he q).comp
      (measurable_id.prodMk (measurable_const (a:=x))) using 1
  have hb (ω : W) : |G ω|^2≤K^2*‖d ω‖^2 := by
    have ho : Measurable (fun p=>old (ω,p)) := hold.comp (measurable_const.prodMk measurable_id)
    have hh := future_input_coarse P hΛ (u ω) (d ω) hsmallPoint θ q hq
      (fun p=>old (ω,p)) ho (fun p=>holdb (ω,p)) n σ target center hσ1 hages hi hhi hstop x
    have hdom : |G ω|≤K*‖d ω‖ := by
      rw [abs_of_nonneg hh.1]
      convert! hh.2 using 1
      dsimp only [K,coarseConstant]
      ring
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hdom 2
  apply (hdi.const_mul (K^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω=>by simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hb ω)


end SHE.NativeResidualInputApplicability
