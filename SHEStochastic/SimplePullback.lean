module

public import SHEStochastic.FilteredPullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FilteredPullback
open MeasureTheory ProbabilityTheory FiniteScalarIto
open scoped NNReal ENNReal
variable {Ω Ξ ι κ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  [DecidableEq ι] [DecidableEq κ]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
  (π : Ξ → Ω) (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π)

def simple (V : Simple F H) : Simple G H :=
  ⟨{ valueBot := fun ξ ↦ V.val.valueBot (π ξ)
     value := V.val.value.mapRange (fun f ξ ↦ f (π ξ)) rfl
     le_of_mem_support_value p hp := V.val.le_of_mem_support_value p (Finsupp.support_mapRange (hf := rfl) hp)
     measurable_valueBot := V.val.measurable_valueBot.comp (hfil 0)
     measurable_value' p _ := by
       change Measurable[G p.1] (V.val.value p ∘ π)
       exact (V.val.measurable_value p).comp (hfil p.1)
     bounded_valueBot := ⟨V.val.valueBotBound, fun ξ ↦ V.val.valueBot_le_valueBotBound (π ξ)⟩
     bounded_value := ⟨V.val.valueBound, fun p _ ξ ↦ by
       simpa only [Finsupp.mapRange_apply] using V.val.value_le_valueBound p (π ξ)⟩ },
   fun p hp ↦ V.property p (Finsupp.support_mapRange (hf := rfl) hp)⟩

theorem simple_apply (V : Simple F H) (t : ℝ≥0) (ξ : Ξ) :
    (simple π hfil V).val t ξ = V.val t (π ξ) := by
  rw [SimpleProcess.apply_eq, SimpleProcess.apply_eq]
  change ({(0 : ℝ≥0)} : Set ℝ≥0).indicator (fun _ ↦ V.val.valueBot (π ξ)) t +
    (V.val.value.mapRange (fun f ξ ↦ f (π ξ)) rfl).sum
      (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ξ) t) = _
  rw [Finsupp.sum_mapRange_index (by intro p; simp)]
  rfl

theorem embedding_simple (hπ : MeasurePreserving π ν μ) (V : Simple F H) :
    input π hπ hfil (embedding F μ H V) = embedding G ν H (simple π hfil V) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  apply Lp.ext
  filter_upwards [input_ae π hπ hfil (embedding F μ H V),
    (input_preserving π hπ hfil).quasiMeasurePreserving.ae
      (FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) V.val).coeFn_toLp,
    (FilteredItoCLM.memLp_uncurry_trim_T (𝓖 := G) (μ := ν) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) (simple π hfil V).val).coeFn_toLp]
      with p h1 h2 h3
  change embedding F μ H V (timeMap π p) = _ at h2
  change embedding G ν H (simple π hfil V) p = _ at h3
  rw [h1, h2, h3]
  exact (simple_apply π hfil V p.1 p.2).symm

theorem simpleValue_naturality (P : Family F μ H ι) (Q : Family G ν H κ)
    (i : ι) (j : κ) (hW : ∀ t ξ, Q.W j t ξ = P.W i t (π ξ)) (V : Simple F H) (ξ : Ξ) :
    simpleValue Q.toCoordinates j (simple π hfil V) ξ = simpleValue P.toCoordinates i V (π ξ) := by
  change (V.val.value.mapRange (fun f ξ ↦ f (π ξ)) rfl).sum
      (fun p v ↦ v ξ * (Q.W j p.2 ξ - Q.W j p.1 ξ)) =
    V.val.value.sum (fun p v ↦ v (π ξ) * (P.W i p.2 (π ξ) - P.W i p.1 (π ξ)))
  rw [Finsupp.sum_mapRange_index (by intro p; simp)]
  apply Finsupp.sum_congr
  intro p _
  rw [hW, hW]

/-- Scalar integration commutes with any filtration-preserving probability
pullback whose driver is literally the original driver composed with π.
The proof reuses simple sums and their L2 density, with no stochastic input. -/
theorem rawIsometry_naturality (hπ : MeasurePreserving π ν μ)
    (P : Family F μ H ι) (Q : Family G ν H κ)
    (i : ι) (j : κ) (hW : ∀ t ξ, Q.W j t ξ = P.W i t (π ξ))
    (f : Lp ℝ 2 (inputMeasure F μ H)) :
    rawIsometry Q.toCoordinates j (input π hπ hfil f) = output π hπ (rawIsometry P.toCoordinates i f) := by
  refine congrFun (DenseRange.equalizer (embedding_dense F μ H)
    ((rawIsometry Q.toCoordinates j).continuous.comp (input π hπ hfil).continuous)
    ((output π hπ).continuous.comp (rawIsometry P.toCoordinates i).continuous)
    (funext fun V ↦ ?_)) f
  simp only [Function.comp_apply]
  rw [embedding_simple, rawIsometry_simple, rawIsometry_simple]
  apply Lp.ext
  filter_upwards [(memLp_simpleValue Q.toCoordinates j (simple π hfil V)).coeFn_toLp,
    output_ae π hπ (simpleLp P.toCoordinates i V),
    hπ.quasiMeasurePreserving.ae (memLp_simpleValue P.toCoordinates i V).coeFn_toLp] with ξ h1 h2 h3
  change simpleLp Q.toCoordinates j (simple π hfil V) ξ = _ at h1
  change simpleLp P.toCoordinates i V (π ξ) = _ at h3
  rw [h1, h2, h3]
  exact simpleValue_naturality π hfil P Q i j hW V ξ

end SHEStochastic.FilteredPullback
