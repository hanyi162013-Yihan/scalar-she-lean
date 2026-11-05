module

public import SHEStochastic.HilbertSimpleInputs
public import SHEStochastic.FilteredSimplePartition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertSimplePartition
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C]
  [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- The common disjoint time cells of a bounded predictable simple row.
The coefficient on each cell is measurable at its left endpoint. -/
def cell (V : HilbertSimpleInputs.bounded (E := C) F H) (k : ℕ) :
    HilbertSimpleInputs.bounded (E := C) F H :=
  HilbertSimpleInputs.step (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))
    (marshalPart_mono F H V.val V.property (Nat.le_succ k))
    (marshalPart_le_T F H V.val V.property (k + 1))
    (marshalMult F H V.val k) (stronglyMeasurable_marshalMult F H V.val k)
    ((V.val.value.support.card : ℝ) * V.val.valueBound)
    (marshalMult_norm_le F H V.val k)

/-- Refinement into disjoint cells preserves the actual predictable L2
input. Values at time zero have zero time measure. -/
theorem embedding_sum (V : HilbertSimpleInputs.bounded (E := C) F H) {N : ℕ}
    (hN : marshalPart F H V.val N = H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    (∑ k ∈ Finset.range N, HilbertSimpleInputs.embedding F μ H (cell V k)) =
      HilbertSimpleInputs.embedding F μ H V := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  have hsupp : ∀ᵐ p ∂ν, p.1 ∈ Set.Ioc 0 H :=
    FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)
  have hcells : ∀ᵐ p ∂ν, ∀ k : ℕ,
      HilbertSimpleInputs.embedding F μ H (cell V k) p = (cell V k).val p.1 p.2 :=
    ae_all_iff.mpr (fun k ↦ HilbertSimpleInputs.embedding_ae F μ H (cell V k))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range N)
    (fun k ↦ HilbertSimpleInputs.embedding F μ H (cell V k)),
    HilbertSimpleInputs.embedding_ae F μ H V, hsupp, hcells] with p hsum hv hp hc
  rw [hsum, hv]
  simp only [Finset.sum_apply]
  simp_rw [hc, cell, HilbertSimpleInputs.step_apply]
  exact sum_cells_map F H V.val V.property hN hp.1 hp.2 id p.2

/-- On the same refinement, any function of the row is reconstructed
pointwise away from the initial endpoint. -/
theorem sum_map (V : HilbertSimpleInputs.bounded (E := C) F H) {N : ℕ}
    (hN : marshalPart F H V.val N = H) {r : ℝ≥0} (hr : r ∈ Set.Ioc 0 H)
    {G : Type*} [AddCommMonoid G] [Module ℝ G] (f : C → G) (ω : Ω) :
    (∑ k ∈ Finset.range N,
      (Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))).indicator
        (fun _ ↦ f (marshalMult F H V.val k ω)) r) = f (V.val r ω) :=
  sum_cells_map F H V.val V.property hN hr.1 hr.2 f ω

/-- Integration of a constant on one time cell gives its actual length,
with the same finite-horizon time measure as the native integral. -/
theorem integral_cell_const (a b : ℝ≥0) (hab : a ≤ b) (hbH : b ≤ H) (c : ℝ) :
    (∫ r, (Set.Ioc a b).indicator (fun _ ↦ c) r
      ∂MathFin.ItoIntegralCLM.timeMeasure_T H) = ((b : ℝ) - a) * c := by
  have hsub : Set.Ioc a b ⊆ Set.Ioc (0 : ℝ≥0) H := fun r hr ↦
    ⟨lt_of_le_of_lt zero_le hr.1, hr.2.trans hbH⟩
  have hm : (MathFin.ItoIntegralCLM.timeMeasure_T H) (Set.Ioc a b) =
      ENNReal.ofReal ((b : ℝ) - a) := by
    rw [MathFin.ItoIntegralCLM.timeMeasure_T, Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.mpr hsub, MathFin.ItoIntegralL2.timeMeasure_Ioc]
  rw [integral_indicator measurableSet_Ioc, setIntegral_const]
  simp only [measureReal_def, hm, ENNReal.toReal_ofReal (sub_nonneg.mpr
    (show (a : ℝ) ≤ b from hab)), smul_eq_mul]

/-- Every sample path of a bounded simple row is square integrable in
time; joint predictability supplies the time-section measurability. -/
theorem path_memLp (V : HilbertSimpleInputs.bounded (E := C) F H) (ω : Ω) :
    MemLp (fun r ↦ V.val r ω) 2 (MathFin.ItoIntegralCLM.timeMeasure_T H) := by
  have hm := V.val.isStronglyPredictable.mono F.predictable_le_prod
  have hpath : StronglyMeasurable (fun r ↦ V.val r ω) :=
    hm.comp_measurable (measurable_id.prodMk measurable_const)
  obtain ⟨K, hK⟩ := V.val.coe_bounded
  exact MemLp.of_bound hpath.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun r ↦ hK r ω)

/-- Integration over all common cells is integration over the fixed
horizon, for any integrable time function. -/
theorem integral_partition (V : HilbertSimpleInputs.bounded (E := C) F H) {N : ℕ}
    (hN : marshalPart F H V.val N = H) (f : ℝ≥0 → ℝ)
    (hf : Integrable f (MathFin.ItoIntegralCLM.timeMeasure_T H)) :
    (∑ k ∈ Finset.range N,
      ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)), f r
        ∂MathFin.ItoIntegralCLM.timeMeasure_T H) =
      ∫ r, f r ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
  let νt := MathFin.ItoIntegralCLM.timeMeasure_T H
  have hi (k : ℕ) := hf.indicator (measurableSet_Ioc
    (a := marshalPart F H V.val k) (b := marshalPart F H V.val (k + 1)))
  simp_rw [← integral_indicator measurableSet_Ioc]
  rw [← integral_finset_sum _ (fun k _ ↦ hi k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have he (k : ℕ) :
      (Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))).indicator f r =
      (Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))).indicator
        (fun _ ↦ (1 : ℝ)) r * f r := by
    by_cases hk : r ∈ Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))
    · simp [Set.indicator_of_mem hk]
    · simp [Set.indicator_of_notMem hk]
  simp_rw [he]
  rw [← Finset.sum_mul, sum_cell_indicator_eq_one F H V.val V.property hN hr.1 hr.2, one_mul]

/-- Refining a simple row preserves its pathwise squared energy exactly.
This uses the same cells as `embedding_sum`, so no separate approximation
or stochastic identity is hidden in the energy bookkeeping. -/
theorem energy_sum (V : HilbertSimpleInputs.bounded (E := C) F H) {N : ℕ}
    (hN : marshalPart F H V.val N = H) (ω : Ω) :
    (∑ k ∈ Finset.range N,
      (((marshalPart F H V.val (k + 1) : ℝ≥0) : ℝ) - marshalPart F H V.val k) *
        ‖marshalMult F H V.val k ω‖ ^ 2) =
      ∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H := by
  classical
  let νt := MathFin.ItoIntegralCLM.timeMeasure_T H
  let f (k : ℕ) (r : ℝ≥0) :=
    (Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))).indicator
      (fun _ ↦ ‖marshalMult F H V.val k ω‖ ^ 2) r
  have hf (k : ℕ) : Integrable (f k) νt := (integrable_const _).indicator measurableSet_Ioc
  have hs : (fun r ↦ ∑ k ∈ Finset.range N, f k r) =ᵐ[νt] fun r ↦ ‖V.val r ω‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact sum_map V hN hr (fun x ↦ ‖x‖ ^ 2) ω
  rw [← integral_congr_ae hs, integral_finset_sum _ (fun k _ ↦ hf k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact (integral_cell_const _ _
    (marshalPart_mono F H V.val V.property (Nat.le_succ k))
    (marshalPart_le_T F H V.val V.property (k + 1)) _).symm

end SHEStochastic.HilbertSimplePartition
