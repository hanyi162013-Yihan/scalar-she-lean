module

public import SHE.HaarCellEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.DyadicCellRefinement
open MeasureTheory SHE SHE.FiniteHaar SHE.CircleHeat

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- The existing scalar step-function refinement identifies actual
coarse and fine circle cells almost everywhere, independently of the
space of values subsequently integrated on those cells. -/
theorem ancestor_ae (n r : ℕ) (i : Grid n) :
    ∀ᵐ y ∂μ, y∈cellSet n i ↔
      ancestorLeaf n r ((gridCellEquiv (n+r)).symm (cellIndex (n+r) y))=i := by
  have hI := gridStep_ae_cellIndex (n+r)
    (fun z => (Pi.single i (1 : ℝ) : Grid n → ℝ) (ancestorLeaf n r z))
  rw [gridStep_ancestor] at hI
  filter_upwards [gridStep_ae_cellIndex n (Pi.single i (1 : ℝ)), hI] with y hi hj
  have heq := hi.symm.trans hj
  rw [cellSet_iff]
  constructor
  · intro hc
    by_contra hp
    simp [hc, hp] at heq
  · intro hp
    by_contra hc
    simp [hc, hp] at heq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem indicator_ae (n r : ℕ) (i : Grid n) (f : AddCircle (1 : ℝ) → E) :
    (cellSet n i).indicator f =ᵐ[μ] fun y => ∑ z : Grid (n+r),
      if ancestorLeaf n r z=i then (cellSet (n+r) z).indicator f y else 0 := by
  filter_upwards [ancestor_ae n r i] with y hy
  let z₀ := (gridCellEquiv (n+r)).symm (cellIndex (n+r) y)
  have hself : y∈cellSet (n+r) z₀ := (cellSet_iff _ _ _).mpr rfl
  rw [Finset.sum_eq_single z₀]
  · by_cases hc : y∈cellSet n i
    · rw [Set.indicator_of_mem hc, if_pos (hy.mp hc), Set.indicator_of_mem hself]
    · rw [Set.indicator_of_notMem hc, if_neg (fun h => hc (hy.mpr h))]
  · intro z hz hne
    have hn : y∉cellSet (n+r) z := fun h => hne ((cellSet_iff _ _ _).mp h).symm
    by_cases ha : ancestorLeaf n r z=i <;> simp [ha, Set.indicator_of_notMem hn]
  · simp

/-- Actual Banach-valued interval masses refine by summing the finer
cell masses. In particular this applies to covariance matrices. -/
theorem integral (n r : ℕ) (i : Grid n) (f : AddCircle (1 : ℝ) → E) (hf : Integrable f μ) :
    (∫ y in cellSet n i, f y ∂μ) = ∑ z : Grid (n+r),
      if ancestorLeaf n r z=i then ∫ y in cellSet (n+r) z, f y ∂μ else 0 := by
  have hint (z : Grid (n+r)) : Integrable
      (fun y => if ancestorLeaf n r z=i then (cellSet (n+r) z).indicator f y else 0) μ := by
    by_cases hz : ancestorLeaf n r z=i
    · simpa only [hz, if_true] using hf.indicator (measurableSet_cellSet _ _)
    · simp only [hz, if_false]
      exact integrable_zero _ _ _
  rw [← integral_indicator (measurableSet_cellSet n i)]
  rw [integral_congr_ae (indicator_ae n r i f), integral_finsetSum _ (fun z _ => hint z)]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases ha : ancestorLeaf n r z=i
  · simp only [ha, if_true]
    exact integral_indicator (measurableSet_cellSet _ _)
  · simp only [ha, if_false, integral_zero]


/-- Every spatial point belongs to exactly one cell of each fixed grid. -/
theorem partition (n : ℕ) (f : AddCircle (1 : ℝ) → E) (y : AddCircle (1 : ℝ)) :
    (∑ z : Grid n, (cellSet n z).indicator f y)=f y := by
  let z₀ := (gridCellEquiv n).symm (cellIndex n y)
  rw [Finset.sum_eq_single z₀]
  · exact Set.indicator_of_mem ((cellSet_iff _ _ _).mpr rfl) f
  · intro z hz hne
    exact Set.indicator_of_notMem (fun h => hne ((cellSet_iff _ _ _).mp h).symm) f
  · simp

/-- Banach-valued dyadic masses sum to the actual total spatial integral. -/
theorem integral_partition (n : ℕ) (f : AddCircle (1 : ℝ) → E) (hf : Integrable f μ) :
    (∫ y, f y ∂μ)=∑ z : Grid n, ∫ y in cellSet n z, f y ∂μ := by
  calc
    _ = ∫ y, ∑ z : Grid n, (cellSet n z).indicator f y ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => (partition n f y).symm))
    _ = ∑ z : Grid n, ∫ y, (cellSet n z).indicator f y ∂μ :=
      integral_finsetSum _ (fun z _ => hf.indicator (measurableSet_cellSet n z))
    _ = _ := Finset.sum_congr rfl (fun z _ => integral_indicator (measurableSet_cellSet n z))


/-- Exact spatial length of every periodic dyadic cell. -/
theorem measure_real (n : ℕ) (i : Grid n) : (μ).real (cellSet n i)=(((2^n : ℕ) : ℝ))⁻¹ := by
  let hs := measurableSet_cellSet n i
  let ht : μ (cellSet n i)≠⊤ := measure_ne_top μ _
  let v := indicatorConstLp 2 hs ht (1 : ℂ)
  have he : cellIndicator n i=v := Lp.ext
    ((cellIndicator_ae n i).trans (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := ht) (c := (1 : ℂ))).symm)
  have hn : ‖v‖=Real.sqrt ((μ).real (cellSet n i)) := by
    rw [norm_indicatorConstLp (by norm_num : (2 : ENNReal)≠0) (by norm_num : (2 : ENNReal)≠⊤)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, Real.sqrt_eq_rpow]
  have hh := cellIndicator_norm_sq n i
  rw [he, hn, Real.sq_sqrt (measureReal_nonneg)] at hh
  exact hh

end SHEStochastic.DyadicCellRefinement
