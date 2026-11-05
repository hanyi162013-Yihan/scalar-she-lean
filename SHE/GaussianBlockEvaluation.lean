module

public import SHE.GaussianBlockFrame
public import SHE.RealHeatScore
public import SHE.RealHeatEnergyScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Canonical real Gaussian evaluation scores from genuine finite Hilbert
blocks. The full covariance stays on its actual range through all ranks. -/
namespace SHE.GaussianBlockEvaluation
open Set MeasureTheory AddCircle Real GaussianIncrement GaussianGramScore
  MeasurableGaussianScores GaussianBlockFrame HeatTorus HeatProjection HeatChristoffel RealHeatScore
open scoped InnerProductSpace

/-- Actual physical block representers, their true full-history frame,
and the proved collision-uniform heat evaluation bound imply the canonical
full covariance score envelope. -/
theorem block_evaluation_scoreVariance_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ {g n : ℕ} (t : Fin g → Fin q → ℝ) (a : Fin g → Fin q → UnitAddCircle)
      (ht : ∀ j i, 0 < t j i), (∀ j i, t j i ≤ h) →
      ∀ {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (v : Fin n → H) (C : Fin g → State n →ₗ[ℝ] G)
      (S : ∀ j, State n →ₗ[ℝ] heatSpan (t j) (a j)) (c : Fin g → ℝ) (b : ℝ),
      (∀ j, 0 < c j) → 0 < b →
      (∀ j z, c j * ‖S j z‖ ^ 2 ≤ ‖C j z‖ ^ 2) →
      (∀ z, b * (∑ j, ‖C j z‖ ^ 2) ≤ ‖featureSynthesis v z‖ ^ 2) →
      ∀ (x : UnitAddCircle) (d : State n),
      (∀ z, inner ℝ z d = ∑ j, realEvaluation (t j) (a j) (ht j) x (S j z)) →
      d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range ∧
      scoreVariance (Matrix.gram ℝ v) d ≤
        (K / b) * ∑ j, (c j)⁻¹ * ∑ i, GlobalTorusHeatSpan.weight (t j i) (a j i) x := by
  obtain ⟨h, K, hh, hh1, hK, he⟩ := finite_real_heat_score_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro g n t a ht hth H G _ _ _ _ _ _ v C S c b hc hb hrow hframe x d hd
  choose m hm hp hn using fun j => he (t j) (a j) (ht j) (hth j) (S j) (C j) (c j) (hc j) (hrow j) x
  obtain ⟨r, hr, hpair, hnorm⟩ := combine_representers (featureSynthesis v) C m hb hframe
  have hpair' (z : State n) : inner ℝ (featureSynthesis v z) r = inner ℝ z d := by
    rw [hpair, hd]
    exact Finset.sum_congr rfl (fun j _ => hp j z)
  refine ⟨physical_direction_mem_range v hr hpair', ?_⟩
  rw [physical_scoreVariance_eq v hr hpair']
  calc
    _ ≤ (∑ j, ‖m j‖ ^ 2) / b := hnorm
    _ ≤ (∑ j, (K / c j) * ∑ i, GlobalTorusHeatSpan.weight (t j i) (a j i) x) / b :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => hn j)) hb.le
    _ = _ := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The same actual block construction retains arbitrary squared row scales,
including zero clipped defect factors. -/
theorem block_energy_scoreVariance_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ {g n : ℕ} (t : Fin g → Fin q → ℝ) (a : Fin g → Fin q → UnitAddCircle)
      (ht : ∀ j i, 0 < t j i), (∀ j i, t j i ≤ h) →
      ∀ {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (v : Fin n → H) (C : Fin g → State n →ₗ[ℝ] G)
      (S : ∀ j, State n →ₗ[ℝ] heatSpan (t j) (a j)) (L : Fin g → ℝ) (b : ℝ),
      (∀ j, 0 ≤ L j) → 0 < b →
      (∀ j z, ‖S j z‖ ^ 2 ≤ L j ^ 2 * ‖C j z‖ ^ 2) →
      (∀ z, b * (∑ j, ‖C j z‖ ^ 2) ≤ ‖featureSynthesis v z‖ ^ 2) →
      ∀ (x : UnitAddCircle) (d : State n),
      (∀ z, inner ℝ z d = ∑ j, realEvaluation (t j) (a j) (ht j) x (S j z)) →
      d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.gram ℝ v)).range ∧
      scoreVariance (Matrix.gram ℝ v) d ≤
        (K / b) * ∑ j, L j ^ 2 * ∑ i, GlobalTorusHeatSpan.weight (t j i) (a j i) x := by
  obtain ⟨h, K, hh, hh1, hK, he⟩ := RealHeatEnergyScore.finite_real_heat_energy_score_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro g n t a ht hth H G _ _ _ _ _ _ v C S L b hL hb hrow hframe x d hd
  choose m hm hp hn using fun j => he (t j) (a j) (ht j) (hth j) (S j) (C j)
    (fun z => ‖C j z‖ ^ 2) 1 (L j) (by norm_num) (hL j) (hrow j)
    (fun _ => by simp only [one_mul, le_refl]) x
  obtain ⟨r, hr, hpair, hnorm⟩ := combine_representers (featureSynthesis v) C m hb hframe
  have hpair' (z : State n) : inner ℝ (featureSynthesis v z) r = inner ℝ z d := by
    rw [hpair, hd]
    exact Finset.sum_congr rfl (fun j _ => hp j z)
  refine ⟨physical_direction_mem_range v hr hpair', ?_⟩
  rw [physical_scoreVariance_eq v hr hpair']
  simp only [div_one] at hn
  calc
    _ ≤ (∑ j, ‖m j‖ ^ 2) / b := hnorm
    _ ≤ (∑ j, (K * L j ^ 2) * ∑ i, GlobalTorusHeatSpan.weight (t j i) (a j i) x) / b :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => hn j)) hb.le
    _ = _ := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

end SHE.GaussianBlockEvaluation
