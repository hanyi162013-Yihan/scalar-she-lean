module

public import SHE.StoppedMeanEnergy
public import SHE.BlockDefectScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual signed-input clipped-defect energy for genuine translated weighted stopped
histories. The canonical real Gaussian score, covariance, spatial row, and
retained heat factor are all literal objects. -/
namespace SHE.StoppedDefectMeanEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection HeatChristoffelTransfer GaussianGramScore GaussianIncrement
  RealHeatCovarianceMean MeasurableGaussianScores StoppedMeanEnergy BlockDefectScores
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {n : ℕ}

def clippedSynthesis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) : State n →ₗ[ℝ] HeatTorus.CircleL2 :=
  ((heatSpan t a).subtype.restrictScalars ℝ).comp (realDefect σ target a u Λ t hage hactive)

theorem clippedSynthesis_basis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) (i : Fin n) :
    clippedSynthesis σ target a u Λ t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ((1-exp (-Λ * (σ i - u))):ℂ) • unitHeatKernel (t i) (a i) :=
  realDefect_basis σ target a u Λ t hage hactive i

theorem clippedSynthesis_span (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) (z : State n) :
    clippedSynthesis σ target a u Λ t hage hactive z ∈ heatSpan t a :=
  (realDefect σ target a u Λ t hage hactive z).property

theorem translated_basis_stronglyMeasurable
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ i, u < σ i) (i : Fin n) :
    StronglyMeasurable (fun x => clippedSynthesis σ target (fun j => a j + x) u Λ t hage hactive
      (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  have hm := (continuous_translate_action.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : UnitAddCircle =>
      unitHeatKernel (t i) (a i))))).stronglyMeasurable
  have hs := hm.const_smul ((1-exp (-Λ * (σ i - u))):ℂ)
  convert! hs using 1
  funext x
  rw [clippedSynthesis_basis]
  change ((1-exp (-Λ * (σ i - u))):ℂ) • unitHeatKernel (t i) (a i + x) =
    ((1-exp (-Λ * (σ i - u))):ℂ) • translate x (unitHeatKernel (t i) (a i))
  rw [translate_unitHeatKernel (ht i)]

/-- Genuine comparable-age one-input energy for the actual clipped defect
score. The profile may vary with the output translation. Its original full
stopped covariance is used, and the heat operator acts on the signed input. -/
theorem translated_stopped_defect_energy (n : ℕ) :
    ∃ h K θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧ 0 < θ ∧
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hages : ∀ i, σ i ≤ target i)
      (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, u + δ ≤ σ i)
      (B:ℝ),1≤B→(∀i,σ i≤u+B*δ)→
      ∀ (w A : ℝ), 0 < w → 1 ≤ A → (∀ i, w ≤ t i) → (∀ i, t i ≤ A * w) →
      ∀ (c : UnitAddCircle × Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
      (hcb : ∀ x r, 0 ≤ c (x, r) ∧ c (x, r) ≤ U), 0 < ell → (∀ x r, ell ≤ c (x, r)) →
      ∀ d : HeatTorus.CircleL2,
      let S := fun x => clippedSynthesis σ target (fun i => a i + x) u Λ t hage
        (fun i => by linarith [hstop i])
      let V := fun x => StoppedGaussianFeatures.stoppedCovariance σ target
        (nativeCenter (fun i => a i + x)) (fun r => c (x, r)) u
      (∀x,meanDirection (S x) d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (V x)).range) ∧
      Integrable (fun x => scoreVariance (V x) (meanDirection (S x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (V x) (meanDirection (S x) d) ∂haarAddCircle) ≤
        K * (max B 8/δ*min 1 (Λ*δ)^2/ell) * sqrt A * sqrt w * ‖CircleHeat.heat (θ * w) d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, hmean⟩ := translated_scoreVariance_bound n
  refine ⟨h, K, θ, hh, hh1, hK, hθ, ?_⟩
  intro σ target a u Λ hΛ t ht hth hage hages δ hδ hstop B hB hstophi w A hw hA hlo hhi c hc U ell hcb hell hcl d
  let act : ∀ i, u < σ i := fun i => by linarith [hstop i]
  let v := fun x => weightedFeature σ target (nativeCenter (fun i => a i + x))
    (fun r => c (x, r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u
  let S := fun x => clippedSynthesis σ target (fun i => a i + x) u Λ t hage act
  have hrow (x : UnitAddCircle) (z : State n) :
      ‖S x z‖ ≤ sqrt (max B 8/δ*min 1 (Λ*δ)^2/ell) * ‖featureSynthesis (v x) z‖ := by
    have hcE := (weightedSynthesis_full_history_bounds σ target (nativeCenter (fun i => a i + x))
      (fun r => c (x, r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages (hcl x) u z).1
    have hcurr := stopped_current_difference_clipped Finset.univ (fun i => (z i : ℂ)) σ target
      (nativeCenter (fun i => a i + x)) (fun i _ => hages i) hΛ hδ hB (fun i _ => hstop i) (fun i _=>hstophi i)
    have hS : ‖S x z‖ ^ 2 = ‖historyF Finset.univ (fun i => (z i : ℂ)) σ target
        (nativeCenter (fun i => a i + x)) u-historyG Finset.univ (fun i => (z i : ℂ)) σ target
        (nativeCenter (fun i => a i + x)) Λ u‖ ^ 2 :=
      realDefect_norm_sq σ target (fun i => a i + x) u Λ t hage act z
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, sq_sqrt (by positivity : 0 ≤ max B 8/δ*min 1 (Λ*δ)^2/ell), hS]
    have he := mul_le_mul_of_nonneg_left hcE (show 0 ≤ max B 8/δ*min 1 (Λ*δ)^2/ell by positivity)
    have he' : (max B 8/δ*min 1 (Λ*δ)^2) * (fullPhysicalEnergy
        (historyF Finset.univ (fun i => (z i : ℂ)) σ target (nativeCenter (fun i => a i + x))) u).toReal ≤
        (max B 8/δ*min 1 (Λ*δ)^2/ell) * ‖featureSynthesis (v x) z‖ ^ 2 := by
      convert! he using 1
      field_simp
      <;> ring
    exact hcurr.trans (by convert! he' using 1 <;> ring)
  have hm := hmean t a ht hth w A hw hA hlo hhi v S
    (translated_feature_gram_measurable σ target a hages u hc U hcb)
    (translated_basis_stronglyMeasurable σ target a u Λ t ht hage act)
    (sqrt (max B 8/δ*min 1 (Λ*δ)^2/ell)) (sqrt_nonneg _)
    (fun x z => clippedSynthesis_span σ target (fun i => a i + x) u Λ t hage act z) hrow d
  have heq (x : UnitAddCircle) := weightedFeature_gram σ target (nativeCenter (fun i => a i + x))
    (fun r => c (x, r)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u
  change ∀ x, Matrix.gram ℝ (v x) = _ at heq
  simp_rw [heq] at hm
  rw [sq_sqrt (by positivity : 0 ≤ max B 8/δ*min 1 (Λ*δ)^2/ell)] at hm
  refine ⟨?_,hm⟩
  intro x
  have hp:=scoreVariance_projection_bound t (fun i=>a i+x) (S x) (v x)
    (fun z=>clippedSynthesis_span σ target (fun i=>a i+x) u Λ t hage act z)
    (sqrt_nonneg _) (hrow x) d
  rw [heq x] at hp
  exact hp.1

end SHE.StoppedDefectMeanEnergy
