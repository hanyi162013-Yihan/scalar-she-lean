module

public import SHE.RealHeatCovarianceMean
public import SHE.StoppedCanonicalScore
public import SHE.HeatChristoffelTransfer

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual signed-input mean energy for genuine translated weighted stopped
histories. The canonical real Gaussian score, covariance, spatial row, and
retained heat factor are all literal objects. -/
namespace SHE.StoppedMeanEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection HeatChristoffelTransfer GaussianGramScore GaussianIncrement
  RealHeatCovarianceMean MeasurableGaussianScores
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ}

def dampedSynthesis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) : State n →ₗ[ℝ] HeatTorus.CircleL2 :=
  ((heatSpan t a).subtype.restrictScalars ℝ).comp (realDamped σ target a u Λ t hage hactive)

theorem dampedSynthesis_basis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) (i : Fin n) :
    dampedSynthesis σ target a u Λ t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i) =
      (exp (-Λ * (σ i - u)) : ℂ) • unitHeatKernel (t i) (a i) :=
  realDamped_basis σ target a u Λ t hage hactive i

theorem dampedSynthesis_span (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) (z : State n) :
    dampedSynthesis σ target a u Λ t hage hactive z ∈ heatSpan t a :=
  (realDamped σ target a u Λ t hage hactive z).property

theorem translated_basis_stronglyMeasurable
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) (i : Fin n) :
    StronglyMeasurable (fun x => dampedSynthesis σ target (fun j => a j + x) u Λ t hage hactive
      (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  have hm := (continuous_translate_action.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : UnitAddCircle =>
      unitHeatKernel (t i) (a i))))).stronglyMeasurable
  have hs := hm.const_smul (exp (-Λ * (σ i - u)) : ℂ)
  convert! hs using 1
  funext x
  rw [dampedSynthesis_basis]
  change (exp (-Λ * (σ i - u)) : ℂ) • unitHeatKernel (t i) (a i + x) =
    (exp (-Λ * (σ i - u)) : ℂ) • translate x (unitHeatKernel (t i) (a i))
  rw [translate_unitHeatKernel (ht i)]

def translatedFamily (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) :
    VariableObservations.Family UnitAddCircle n where
  observations x i := ⟨σ i, target i, nativeCenter (fun j => a j + x) i⟩
  stop_measurable _ := measurable_const
  target_measurable _ := measurable_const
  center_measurable i := (CircleNormalization.continuous_scale 1 (2 * π)).measurable.comp
    ((continuous_const.add continuous_id).measurable : Measurable (fun x : UnitAddCircle => a i + x))

theorem translated_feature_gram_measurable
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) {c : UnitAddCircle × Domain → ℝ}
    (hc : Measurable c) (U : ℝ) (hcb : ∀ x r, 0 ≤ c (x, r) ∧ c (x, r) ≤ U) :
    Measurable (fun x => Matrix.gram ℝ
      (weightedFeature σ target (nativeCenter (fun i => a i + x)) (fun r => c (x, r))
        (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages q)) := by
  have hm := StoppedGaussianFields.covariance_measurable (translatedFamily σ target a) hc
    (measurable_const (a := q))
  convert! hm using 1
  funext x
  exact weightedFeature_gram σ target (nativeCenter (fun i => a i + x)) (fun r => c (x, r))
    (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages q

/-- Genuine comparable-age one-input energy for the actual damped mean
score. The profile may vary with the output translation. Its original full
stopped covariance is used, and the heat operator acts on the signed input. -/
theorem translated_stopped_mean_energy (n : ℕ) :
    ∃ h K θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧ 0 < θ ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hages : ∀ i, σ i ≤ target i)
      (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, u + δ ≤ σ i),
      ∀ (w A : ℝ), 0 < w → 1 ≤ A → (∀ i, w ≤ t i) → (∀ i, t i ≤ A * w) →
      ∀ (c : UnitAddCircle × Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
      (hcb : ∀ x r, 0 ≤ c (x, r) ∧ c (x, r) ≤ U), 0 < ell → (∀ x r, ell ≤ c (x, r)) →
      ∀ d : HeatTorus.CircleL2,
      let S := fun x => dampedSynthesis σ target (fun i => a i + x) u Λ t hage
        (fun i => by linarith [hstop i])
      let V := fun x => StoppedGaussianFeatures.stoppedCovariance σ target
        (nativeCenter (fun i => a i + x)) (fun r => c (x, r)) u
      Integrable (fun x => scoreVariance (V x) (meanDirection (S x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (V x) (meanDirection (S x) d) ∂haarAddCircle) ≤
        K * (2 / (ell * δ)) * sqrt A * sqrt w * ‖CircleHeat.heat (θ * w) d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, hmean⟩ := translated_scoreVariance_bound n
  refine ⟨h, K, θ, hh, hh1, hK, hθ, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages δ hδ hstop w A hw hA hlo hhi c hc U ell hcb hell hcl d
  let act : ∀ i, u < σ i := fun i => by linarith [hstop i]
  let v := fun x => weightedFeature σ target (nativeCenter (fun i => a i + x))
    (fun r => c (x, r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u
  let S := fun x => dampedSynthesis σ target (fun i => a i + x) u Λ t hage act
  have hrow (x : UnitAddCircle) (z : State n) :
      ‖S x z‖ ≤ sqrt (2 / (ell * δ)) * ‖featureSynthesis (v x) z‖ := by
    have hcE := (weightedSynthesis_full_history_bounds σ target (nativeCenter (fun i => a i + x))
      (fun r => c (x, r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages (hcl x) u z).1
    have hcurr := stopped_damped_current_row_bound Finset.univ (fun i => (z i : ℂ)) σ target
      (nativeCenter (fun i => a i + x)) (fun i _ => hages i) hΛ hδ (fun i _ => hstop i)
    have hS : ‖S x z‖ ^ 2 = ‖historyG Finset.univ (fun i => (z i : ℂ)) σ target
        (nativeCenter (fun i => a i + x)) Λ u‖ ^ 2 :=
      realDamped_norm_sq σ target (fun i => a i + x) u Λ t hage act z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, sq_sqrt (by positivity : 0 ≤ 2 / (ell * δ)), hS]
    have he := mul_le_mul_of_nonneg_left hcE (show 0 ≤ 2 / (ell * δ) by positivity)
    have he' : (2 / δ) * (fullPhysicalEnergy
        (historyF Finset.univ (fun i => (z i : ℂ)) σ target (nativeCenter (fun i => a i + x))) u).toReal ≤
        (2 / (ell * δ)) * ‖featureSynthesis (v x) z‖ ^ 2 := by
      convert! he using 1
      field_simp
    exact hcurr.trans he'
  have hm := hmean t a ht hth w A hw hA hlo hhi v S
    (translated_feature_gram_measurable σ target a hages u hc U hcb)
    (translated_basis_stronglyMeasurable σ target a u Λ t ht hage act)
    (sqrt (2 / (ell * δ))) (sqrt_nonneg _)
    (fun x z => dampedSynthesis_span σ target (fun i => a i + x) u Λ t hage act z) hrow d
  have heq (x : UnitAddCircle) := weightedFeature_gram σ target (nativeCenter (fun i => a i + x))
    (fun r => c (x, r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u
  change ∀ x, Matrix.gram ℝ (v x) = _ at heq
  simp_rw [heq] at hm
  rw [sq_sqrt (by positivity : 0 ≤ 2 / (ell * δ))] at hm
  exact hm

end SHE.StoppedMeanEnergy
