module

public import SHEStochastic.HilbertSimplePartition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertSimpleTimeCut
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C]
  [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

def timeRow (a : ℝ≥0) (haH : a ≤ H) : HilbertSimpleInputs.bounded (E := ℝ) F H :=
  HilbertSimpleInputs.step a H haH le_rfl (fun _ ↦ 1) stronglyMeasurable_const 1
    (fun _ ↦ by simp)

def cutProcess (a : ℝ≥0) (haH : a ≤ H) (V : HilbertSimpleInputs.bounded (E := C) F H) :
    SimpleProcess C F :=
  SimpleProcess.map₂ (ContinuousLinearMap.lsmul ℝ ℝ) (timeRow (F := F) a haH).val V.val

theorem cut_bounds (a : ℝ≥0) (haH : a ≤ H)
    (V : HilbertSimpleInputs.bounded (E := C) F H) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ (cutProcess a haH V).value.support) : a ≤ p.1 ∧ p.2 ≤ H := by
  change p ∈ ((timeRow (F := F) a haH).val.value.sum fun s v ↦ V.val.value.sum fun t w ↦
    Finsupp.single (s.1 ⊔ t.1, s.2 ⊓ t.2)
      (if t.1 ≤ s.2 ∧ s.1 ≤ t.2 then
        (fun ω ↦ (ContinuousLinearMap.lsmul ℝ ℝ) (v ω) (w ω)) else 0)).support at hp
  obtain ⟨s, hs, hp⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hp)
  obtain ⟨t, ht, hp⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hp)
  have hp' := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
  change s ∈ (Finsupp.single (a, H) (fun _ : Ω ↦ (1 : ℝ))).support at hs
  obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  subst p
  exact ⟨le_sup_left, inf_le_left⟩

def cut (a : ℝ≥0) (haH : a ≤ H) (V : HilbertSimpleInputs.bounded (E := C) F H) :
    HilbertSimpleInputs.bounded (E := C) F H :=
  ⟨cutProcess a haH V, fun _ hp ↦ (cut_bounds a haH V hp).2⟩

theorem cut_starts_after (a : ℝ≥0) (haH : a ≤ H)
    (V : HilbertSimpleInputs.bounded (E := C) F H) :
    ∀ p ∈ (cut a haH V).val.value.support, a ≤ p.1 :=
  fun _ hp ↦ (cut_bounds a haH V hp).1

theorem cut_apply (a : ℝ≥0) (haH : a ≤ H)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (r : ℝ≥0) (ω : Ω) :
    (cut a haH V).val r ω = (Set.Ioc a H).indicator (fun r ↦ V.val r ω) r := by
  change (cutProcess a haH V) r ω = _
  simp only [cutProcess, SimpleProcess.coe_map₂]
  change (ContinuousLinearMap.lsmul ℝ ℝ) ((timeRow (F := F) a haH).val r ω) (V.val r ω) = _
  simp only [timeRow, HilbertSimpleInputs.step_apply]
  by_cases hr : r ∈ Set.Ioc a H
  · simp [Set.indicator_of_mem hr]
  · simp [Set.indicator_of_notMem hr]

/-- Cutting a simple approximation after the same time as the target
can only decrease its L2 error. This reuses the existing density theorem
without constructing another predictable measure or completion map. -/
theorem embedding_cut_sub_le (a : ℝ≥0) (haH : a ≤ H)
    (V : HilbertSimpleInputs.bounded (E := C) F H) (u : Lp C 2 ν)
    (hu : ∀ᵐ p ∂ν, p.1 ≤ a → u p = 0) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    ‖HilbertSimpleInputs.embedding F μ H (cut a haH V) - u‖ ≤
      ‖HilbertSimpleInputs.embedding F μ H V - u‖ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (HilbertSimpleInputs.embedding F μ H (cut a haH V)) u,
    Lp.coeFn_sub (HilbertSimpleInputs.embedding F μ H V) u,
    HilbertSimpleInputs.embedding_ae F μ H (cut a haH V),
    HilbertSimpleInputs.embedding_ae F μ H V, hu,
    FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hs ht hc hv hzero hp
  rw [hs, ht]
  simp only [Pi.sub_apply]
  rw [hc, hv]
  change ‖(cut a haH V).val p.1 p.2 - u p‖ ≤ ‖V.val p.1 p.2 - u p‖
  rw [cut_apply]
  by_cases hpa : a < p.1
  · rw [Set.indicator_of_mem (show p.1 ∈ Set.Ioc a H from ⟨hpa, hp.2⟩)]
  · rw [Set.indicator_of_notMem (show p.1 ∉ Set.Ioc a H from fun h ↦ hpa h.1),
      hzero (le_of_not_gt hpa), sub_zero, norm_zero]
    exact norm_nonneg _

end SHEStochastic.HilbertSimpleTimeCut
