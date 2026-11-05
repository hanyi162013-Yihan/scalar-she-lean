module

public import SHE.StoppedMeanEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.StoppedMeanRange
open Set MeasureTheory AddCircle Real Finset StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  GaussianGramScore GaussianIncrement StoppedMeanEnergy RealHeatCovarianceMean
  MeasurableGaussianScores HeatProjection
open scoped InnerProductSpace
local instance stoppedMeanRange_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def currentSynthesis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - q = 4 * π ^ 2 * t i)
    (hactive : ∀ i, q < σ i) : State n →ₗ[ℝ] HeatTorus.CircleL2 :=
  ((heatSpan t a).subtype.restrictScalars ℝ).comp (realCurrent σ target a q t hage hactive)

theorem currentSynthesis_basis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - q = 4 * π ^ 2 * t i)
    (hactive : ∀ i, q < σ i) (i : Fin n) :
    currentSynthesis σ target a q t hage hactive (EuclideanSpace.basisFun (Fin n) ℝ i) =
      unitHeatKernel (t i) (a i) := realCurrent_basis σ target a q t hage hactive i

/-- An actual full stopped-history row bound implies both covariance-range
membership and the physical signed-input Gaussian score bound. -/
theorem mean_range_of_history_bound
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (t : Fin n → ℝ) (hages : ∀ i, σ i ≤ target i)
    (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (S : State n →ₗ[ℝ] HeatTorus.CircleL2) (hspan : ∀ z, S z ∈ heatSpan t a)
    (L : ℝ) (hL : 0 ≤ L)
    (hrow : ∀ z, ‖S z‖ ^ 2 ≤ L *
      (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) q).toReal)
    (d : HeatTorus.CircleL2) :
    meanDirection S d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ target (nativeCenter a) c q)).range ∧
    scoreVariance (stoppedCovariance σ target (nativeCenter a) c q) (meanDirection S d) ≤
      (L / ell) * ‖(heatSpan t a).starProjection d‖ ^ 2 := by
  let v := weightedFeature σ target (nativeCenter a) c hc U hcb hages q
  have hb (z : State n) : ‖S z‖ ≤ sqrt (L / ell) * ‖featureSynthesis v z‖ := by
    have he := (weightedSynthesis_full_history_bounds σ target (nativeCenter a) c hc U hcb hages hcl q z).1
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, sq_sqrt (div_nonneg hL hell.le)]
    calc
      _ ≤ L * (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) q).toReal := hrow z
      _ = (L / ell) * (ell * (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target (nativeCenter a)) q).toReal) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left he (div_nonneg hL hell.le)
  have hh := scoreVariance_projection_bound t a S v hspan (sqrt_nonneg _) hb d
  rw [sq_sqrt (div_nonneg hL hell.le)] at hh
  have he := weightedFeature_gram σ target (nativeCenter a) c hc U hcb hages q
  change Matrix.gram ℝ v = _ at he
  rw [he] at hh
  exact hh

/-- All original stopping indicators and target ages are retained in the
current-mean range calculation. -/
theorem current_mean_range (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - q = 4 * π ^ 2 * t i)
    (hages : ∀ i, σ i ≤ target i) (δ : ℝ) (hδ : 0 < δ)
    (hstop : ∀ i, q + δ ≤ σ i) (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d : HeatTorus.CircleL2) :
    let act : ∀ i, q < σ i := fun i => by linarith [hstop i]
    let S := currentSynthesis σ target a q t hage act
    meanDirection S d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ target (nativeCenter a) c q)).range ∧
    scoreVariance (stoppedCovariance σ target (nativeCenter a) c q) (meanDirection S d) ≤
      ((2 / δ) / ell) * ‖(heatSpan t a).starProjection d‖ ^ 2 := by
  let act : ∀ i, q < σ i := fun i => by linarith [hstop i]
  apply mean_range_of_history_bound σ target a q t hages c hc U ell hcb hell hcl
    (currentSynthesis σ target a q t hage act) (fun z => (realCurrent σ target a q t hage act z).property)
    (2 / δ) (by positivity) _ d
  intro z
  change ‖currentHeatRow σ target a q t hage act (fun i => (z i : ℂ))‖ ^ 2 ≤ _
  rw [currentHeatRow_norm_sq]
  exact stopped_current_row_bound univ (fun i => (z i : ℂ)) σ target (nativeCenter a)
    (fun i _ => hages i) hδ (fun i _ => hstop i)

theorem damped_mean_range (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q Λ : ℝ)
    (hΛ : 0 < Λ) (t : Fin n → ℝ) (hage : ∀ i, target i - q = 4 * π ^ 2 * t i)
    (hages : ∀ i, σ i ≤ target i) (δ : ℝ) (hδ : 0 < δ)
    (hstop : ∀ i, q + δ ≤ σ i) (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d : HeatTorus.CircleL2) :
    let act : ∀ i, q < σ i := fun i => by linarith [hstop i]
    let S := dampedSynthesis σ target a q Λ t hage act
    meanDirection S d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ target (nativeCenter a) c q)).range ∧
    scoreVariance (stoppedCovariance σ target (nativeCenter a) c q) (meanDirection S d) ≤
      ((2 / δ) / ell) * ‖(heatSpan t a).starProjection d‖ ^ 2 := by
  let act : ∀ i, q < σ i := fun i => by linarith [hstop i]
  apply mean_range_of_history_bound σ target a q t hages c hc U ell hcb hell hcl
    (dampedSynthesis σ target a q Λ t hage act) (dampedSynthesis_span σ target a q Λ t hage act)
    (2 / δ) (by positivity) _ d
  intro z
  rw [show ‖dampedSynthesis σ target a q Λ t hage act z‖ ^ 2 =
    ‖historyG univ (fun i => (z i : ℂ)) σ target (nativeCenter a) Λ q‖ ^ 2 from
    realDamped_norm_sq σ target a q Λ t hage act z]
  exact stopped_damped_current_row_bound univ (fun i => (z i : ℂ)) σ target (nativeCenter a)
    (fun i _ => hages i) hΛ hδ (fun i _ => hstop i)

end SHE.StoppedMeanRange
