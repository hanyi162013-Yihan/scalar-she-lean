module

public import SHE.HeatOverlap

/-! Actual almost orthogonality of two finite compact heat spans, uniformly
over all within-cluster collisions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatCluster
open MeasureTheory Real SHE.HeatLine SHE.HeatOverlap SHE.HeatSpanCluster

theorem continuous_heat_span {q : ℕ} (t a : Fin q → ℝ) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i)))) :
    Continuous (fun x : ℝ => f (x : ℂ)) :=
  (contDiff_gaussian_span (fun i => heatParameter (t i) (a i)) f
    (heat_span_gaussian t a f hf)).continuous.comp Complex.continuous_ofReal

/-- A genuine physical separation threshold for two arbitrary compact heat
clusters. The conclusion concerns their actual line inner product. -/
theorem compact_heat_clusters_almost_orthogonal (q r : ℕ) {δ B ε : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (t a : Fin q → ℝ) (u b : Fin r → ℝ) (T U c d : ℝ), 0 < T → 0 < U →
      (∀ i, δ * T ≤ t i) → (∀ i, t i ≤ T) → (∀ i, |a i - c| ≤ B * sqrt T) →
      (∀ i, δ * U ≤ u i) → (∀ i, u i ≤ U) → (∀ i, |b i - d| ≤ B * sqrt U) →
      (T > L * U ∨ U > L * T ∨ |c - d| > L * sqrt (max T U)) →
      ∀ (f g : ℂ → ℂ),
      f ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (t i) (a i))) →
      g ∈ Submodule.span ℂ (Set.range (fun i => heatEntire (u i) (b i))) →
      Integrable (fun x : ℝ => f (x : ℂ) * star (g (x : ℂ))) ∧
      ‖∫ x : ℝ, f (x : ℂ) * star (g (x : ℂ))‖ ≤
        ε * sqrt (∫ x : ℝ, ‖f (x : ℂ)‖ ^ 2) * sqrt (∫ x : ℝ, ‖g (x : ℂ)‖ ^ 2) := by
  obtain ⟨C, hC, hcluster⟩ := compact_heat_cluster_envelope q hδ hB
  obtain ⟨D, hD, hcluster'⟩ := compact_heat_cluster_envelope r hδ hB
  let A : ℝ := sqrt (8 * π * C * D)
  have hA : 0 < A := sqrt_pos.mpr (by positivity)
  obtain ⟨L, hL, hsep⟩ := exists_overlap_separation_threshold (div_pos hε hA)
  refine ⟨L, hL, ?_⟩
  intro t a u b T U c d hT hU ht htT ha hu huU hb hseparated f g hf hg
  obtain ⟨_, hfb⟩ := hcluster t a T c hT ht htT ha f hf
  obtain ⟨_, hgb⟩ := hcluster' u b U d hU hu huU hb g hg
  let E : ℝ := ∫ x : ℝ, ‖f (x : ℂ)‖ ^ 2
  let F : ℝ := ∫ x : ℝ, ‖g (x : ℂ)‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hF : 0 ≤ F := integral_nonneg (fun _ => sq_nonneg _)
  obtain ⟨hi, hbnd⟩ := heat_envelope_cross_bound_normalized
    (continuous_heat_span t a f hf).aestronglyMeasurable
    (continuous_heat_span u b g hg).aestronglyMeasurable
    hC.le hD.le hE hF hT hU hfb hgb
  refine ⟨hi, ?_⟩
  have hw := hsep T U c d hT hU hseparated
  calc
    _ ≤ A * sqrt E * sqrt F * overlapWeight T U c d := hbnd
    _ ≤ A * sqrt E * sqrt F * (ε / A) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by dsimp only [E, F]; field_simp

end SHE.HeatCluster
