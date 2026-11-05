module

public import SHEStochastic.ProductBrownianFiniteLaw
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ProductBrownianFiniteLaw
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal
variable {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [DecidableEq ι] [Inhabited ι]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›} {H : ℝ≥0}

def merge {n : ℕ} (a : Fin n → Sum ι ι) (z : WordRecursion.State n × WordRecursion.State n) :
    WordRecursion.State n := WithLp.toLp 2 (fun i ↦ (a i).elim (fun _ ↦ z.1 i) (fun _ ↦ z.2 i))

theorem merge_measurable {n : ℕ} (a : Fin n → Sum ι ι) : Measurable (merge a) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  cases hi : a i <;> simp only [merge, hi, Sum.elim_inl, Sum.elim_inr]
  · exact (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp measurable_fst
  · exact (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp measurable_snd

theorem increment_vector_measurable (P : FiniteScalarIto.Family F μ H ι)
    {n : ℕ} (a : Fin n → ι) (s t : ℝ≥0) :
    Measurable (fun ω ↦ (WithLp.toLp 2 (fun i ↦ P.W (a i) t ω - P.W (a i) s ω) : WordRecursion.State n)) :=
  (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    (Measurable.of_eval fun i ↦ (FiniteScalarIto.measurable_coordinate P.toCoordinates (a i) t).sub
      (FiniteScalarIto.measurable_coordinate P.toCoordinates (a i) s))

theorem future_independent (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
    (n : ℕ) (a : Fin n → Sum ι ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H) :
    Indep (MeasurableSpace.comap (fun z : IndependentNoiseCompletion.Space μ ν ↦
      (WithLp.toLp 2 (fun i ↦ paired P Q (a i) t z - paired P Q (a i) s z) : WordRecursion.State n))
        inferInstance)
      (IndependentNoiseCompletion.filtration μ ν F G s) (IndependentNoiseCompletion.measure μ ν) := by
  let X (ω : Ω) : WordRecursion.State n :=
    WithLp.toLp 2 (fun i ↦ P.W (leftIndex a i) t ω - P.W (leftIndex a i) s ω)
  let Y (ξ : Ξ) : WordRecursion.State n :=
    WithLp.toLp 2 (fun i ↦ Q.W (rightIndex a i) t ξ - Q.W (rightIndex a i) s ξ)
  have hmX := increment_vector_measurable P (leftIndex a) s t
  have hmY := increment_vector_measurable Q (rightIndex a) s t
  have hi := ProductIndependence.independent_completed_past μ ν F G s
    (Measurable.comap_le hmX) (Measurable.comap_le hmY)
    ((P.law n (leftIndex a)).2 s t hst ht) ((Q.law n (rightIndex a)).2 s t hst ht)
  have he : (fun z : IndependentNoiseCompletion.Space μ ν ↦
      (WithLp.toLp 2 (fun i ↦ paired P Q (a i) t z - paired P Q (a i) s z) : WordRecursion.State n)) =
        merge a ∘ Prod.map X Y := by
    funext z
    ext i
    cases hi : a i <;> simp [paired, merge, X, Y, leftIndex, rightIndex, hi]
  rw [he]
  apply indep_of_indep_of_le_left hi
  rw [← MeasurableSpace.comap_prodMap X Y, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (merge_measurable a))

theorem paired_adapted (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
    (i : Sum ι ι) (t : ℝ≥0) :
    Measurable[IndependentNoiseCompletion.filtration μ ν F G t] (paired P Q i t) := by
  cases i with
  | inl i =>
      exact ((P.adapted i t).comp (@measurable_fst Ω Ξ (F t) (G t))).mono le_sup_left le_rfl
  | inr i =>
      exact ((Q.adapted i t).comp (@measurable_snd Ω Ξ (F t) (G t))).mono le_sup_left le_rfl

/-- Actual recognized paired Brownian coordinates on the paper's
completed independent product filtration. No stochastic input package is
used to construct these laws or their full-past independence. -/
def family (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι) :
    FiniteScalarIto.Family (IndependentNoiseCompletion.filtration μ ν F G)
      (IndependentNoiseCompletion.measure μ ν) H (Sum ι ι) where
  W := paired P Q
  adapted := paired_adapted P Q
  continuous i z := by cases i with
    | inl i => exact P.continuous i z.1
    | inr i => exact Q.continuous i z.2
  law n a := ⟨fun t ht ↦ finite_law P Q n a t ht, future_independent P Q n a⟩

end SHEStochastic.ProductBrownianFiniteLaw
