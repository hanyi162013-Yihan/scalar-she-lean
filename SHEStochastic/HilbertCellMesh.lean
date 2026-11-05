module

public import SHEStochastic.HilbertSimplePartition
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertCellMesh
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C]
  [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0}
  (V : HilbertSimpleInputs.bounded (E := C) F H)

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "T" => marshalPart F H V.val

/-- The common time cells have total weight one on the horizon. Jensen
therefore bounds a Hilbert cell sum without a factor equal to the number
of cells. -/
theorem cell_sum_sq_le (N : ℕ) (hN : T N = H) {r : ℝ≥0} (hr : r ∈ Set.Ioc 0 H)
    (U : ℕ → C) :
    ‖∑ k ∈ Finset.range N, (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ U k) r‖ ^ 2 ≤
      ∑ k ∈ Finset.range N, (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ ‖U k‖ ^ 2) r := by
  let w (k : ℕ) : ℝ := (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ 1) r
  have hw (k : ℕ) : 0 ≤ w k := Set.indicator_nonneg (fun _ _ ↦ zero_le_one) r
  have hsum : (∑ k ∈ Finset.range N, w k) = 1 :=
    sum_cell_indicator_eq_one F H V.val V.property hN hr.1 hr.2
  have he (k : ℕ) : (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ U k) r = w k • U k := by
    by_cases hk : r ∈ Set.Ioc (T k) (T (k + 1)) <;> simp [w, hk]
  have he2 (k : ℕ) : (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ ‖U k‖ ^ 2) r =
      w k • ‖U k‖ ^ 2 := by
    by_cases hk : r ∈ Set.Ioc (T k) (T (k + 1)) <;> simp [w, hk]
  simp_rw [he, he2]
  exact (convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2).map_sum_le
    (fun k _ ↦ hw k) hsum (fun _ _ ↦ Set.mem_univ _)

theorem cell_sum_energy_le (N : ℕ) (hN : T N = H) (U : ℕ → C) :
    (∫ r, ‖∑ k ∈ Finset.range N,
      (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ U k) r‖ ^ 2 ∂νt) ≤
      ∑ k ∈ Finset.range N, (((T (k + 1) : ℝ≥0) : ℝ) - T k) * ‖U k‖ ^ 2 := by
  have hLp : MemLp (fun r ↦ ∑ k ∈ Finset.range N,
      (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ U k) r) 2 νt :=
    memLp_finsetSum _ (fun k _ ↦ (memLp_const (U k)).indicator measurableSet_Ioc.nullMeasurableSet)
  have hi (k : ℕ) := (integrable_const (‖U k‖ ^ 2) :
    Integrable (fun _ : ℝ≥0 ↦ ‖U k‖ ^ 2) νt).indicator
      (measurableSet_Ioc (a := T k) (b := T (k + 1)))
  calc
    _ ≤ ∫ r, ∑ k ∈ Finset.range N,
        (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ ‖U k‖ ^ 2) r ∂νt := by
      apply integral_mono_ae hLp.norm.integrable_sq (integrable_finsetSum _ (fun k _ ↦ hi k))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact cell_sum_sq_le V N hN hr U
    _ = ∑ k ∈ Finset.range N, ∫ r,
        (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ ‖U k‖ ^ 2) r ∂νt :=
      integral_finsetSum _ (fun k _ ↦ hi k)
    _ = _ := Finset.sum_congr rfl (fun k _ ↦ HilbertSimplePartition.integral_cell_const _ _
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))
      (marshalPart_le_T F H V.val V.property (k + 1)) _)

/-- Assemble new left-adapted coefficients on the original common mesh. -/
def assemble (N : ℕ) (U : ℕ → Ω → C)
    (hU : ∀ k, StronglyMeasurable[F (T k)] (U k)) (K : ℝ) (hK : ∀ k ω, ‖U k ω‖ ≤ K) :
    HilbertSimpleInputs.bounded (E := C) F H :=
  ∑ k ∈ Finset.range N, HilbertSimpleInputs.step (T k) (T (k + 1))
    (marshalPart_mono F H V.val V.property (Nat.le_succ k))
    (marshalPart_le_T F H V.val V.property (k + 1)) (U k) (hU k) K (hK k)

theorem assemble_apply (N : ℕ) (U : ℕ → Ω → C)
    (hU : ∀ k, StronglyMeasurable[F (T k)] (U k)) (K : ℝ) (hK : ∀ k ω, ‖U k ω‖ ≤ K)
    (r : ℝ≥0) (ω : Ω) :
    (assemble V N U hU K hK).val r ω =
      ∑ k ∈ Finset.range N, (Set.Ioc (T k) (T (k + 1))).indicator (fun _ ↦ U k ω) r := by
  induction N with
  | zero => simp [assemble]
  | succ N ih =>
    simp only [assemble, Finset.sum_range_succ, Submodule.coe_add, SimpleProcess.coe_add,
      Pi.add_apply, HilbertSimpleInputs.step_apply]
    exact congrArg (fun z : C ↦ z + (Set.Ioc (T N) (T (N + 1))).indicator (fun _ ↦ U N ω) r) ih

theorem assemble_energy_le (N : ℕ) (hN : T N = H) (U : ℕ → Ω → C)
    (hU : ∀ k, StronglyMeasurable[F (T k)] (U k)) (K : ℝ) (hK : ∀ k ω, ‖U k ω‖ ≤ K) (ω : Ω) :
    (∫ r, ‖(assemble V N U hU K hK).val r ω‖ ^ 2 ∂νt) ≤
      ∑ k ∈ Finset.range N, (((T (k + 1) : ℝ≥0) : ℝ) - T k) * ‖U k ω‖ ^ 2 := by
  simp_rw [assemble_apply]
  exact cell_sum_energy_le V N hN (fun k ↦ U k ω)

theorem assemble_loss_le (N : ℕ) (hN : T N = H) (U : ℕ → Ω → C)
    (hU : ∀ k, StronglyMeasurable[F (T k)] (U k)) (K : ℝ) (hK : ∀ k ω, ‖U k ω‖ ≤ K) (ω : Ω) :
    (∫ r, ‖V.val r ω - (assemble V N U hU K hK).val r ω‖ ^ 2 ∂νt) ≤
      ∑ k ∈ Finset.range N, (((T (k + 1) : ℝ≥0) : ℝ) - T k) *
        ‖marshalMult F H V.val k ω - U k ω‖ ^ 2 := by
  have he : (fun r ↦ V.val r ω - (assemble V N U hU K hK).val r ω) =ᵐ[νt]
      (fun r ↦ ∑ k ∈ Finset.range N,
        (Set.Ioc (T k) (T (k + 1))).indicator
          (fun _ ↦ marshalMult F H V.val k ω - U k ω) r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrec := sum_cells_map F H V.val V.property hN hr.1 hr.2 id ω
    simp only [id_eq] at hrec
    rw [← hrec, assemble_apply,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hm : r ∈ Set.Ioc (T k) (T (k + 1)) <;> simp [hm]
  calc
    _ = ∫ r, ‖∑ k ∈ Finset.range N,
        (Set.Ioc (T k) (T (k + 1))).indicator
          (fun _ ↦ marshalMult F H V.val k ω - U k ω) r‖ ^ 2 ∂νt :=
      integral_congr_ae (he.mono fun r hr ↦ congrArg (fun z : C ↦ ‖z‖ ^ 2) hr)
    _ ≤ _ := cell_sum_energy_le V N hN (fun k ↦ marshalMult F H V.val k ω - U k ω)

end SHEStochastic.HilbertCellMesh
