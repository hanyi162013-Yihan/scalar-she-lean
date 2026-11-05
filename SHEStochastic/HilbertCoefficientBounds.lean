module

public import SHEStochastic.HilbertTerminalIto
public import SHEStochastic.WeightedBracketBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.HilbertCoefficientBounds
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

variable {Ω ι κ E : Type*} [MeasurableSpace Ω] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem coordinate (b : HilbertBasis κ ℝ E) (x : Space ι E) (j : κ) :
    (ColumnsHilbertSum.total b).linearIsometryEquiv x j = mapCLM (innerSL ℝ (b j)) x := by
  rw [L2HilbertSum.coordinate, ColumnsHilbertSum.columnUnit_adjoint]

theorem norm_le (b : HilbertBasis κ ℝ E) (x : Space ι E) (j : κ) :
    ‖mapCLM (innerSL ℝ (b j)) x‖ ≤ ‖x‖ := by
  have hh := lp.norm_apply_le_norm (p := 2) (by norm_num)
    ((ColumnsHilbertSum.total b).linearIsometryEquiv x) j
  simpa only [coordinate, LinearIsometryEquiv.norm_map] using hh

/-- Finite coordinate energy is bounded by the full input energy,
pointwise in the original Hilbert column space. -/
theorem sum_sq_le (b : HilbertBasis κ ℝ E) (x : Space ι E) (s : Finset κ) :
    (∑ j ∈ s, ‖mapCLM (innerSL ℝ (b j)) x‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  have hh := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num)
    ((ColumnsHilbertSum.total b).linearIsometryEquiv x) s
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, coordinate, LinearIsometryEquiv.norm_map] using hh

theorem coefficient_ae_trim (b : HilbertBasis κ ℝ E) (u : Process (E := Space ι E) F μ H) (j : κ) :
    HilbertTerminalIto.coefficient F μ H b u j =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      (fun p ↦ mapCLM (innerSL ℝ (b j)) (u p)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change HilbertIsometryLift.sourceEquiv _ b u j =ᵐ[_] _
  rw [HilbertIsometryLift.source_coordinate]
  exact (mapCLM (innerSL ℝ (b j))).coeFn_compLpL u

theorem coefficient_ae (b : HilbertBasis κ ℝ E) (u : Process (E := Space ι E) F μ H) (j : κ) :
    HilbertTerminalIto.coefficient F μ H b u j =ᵐ[energyMeasure μ H]
      (fun p ↦ mapCLM (innerSL ℝ (b j)) (u p)) :=
  ae_eq_of_ae_eq_trim (coefficient_ae_trim b u j)

theorem bounded (b : HilbertBasis κ ℝ E) (u : Process (E := Space ι E) F μ H) (M : ℝ)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M) (j : κ) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      ‖HilbertTerminalIto.coefficient F μ H b u j p‖ ≤ M := by
  filter_upwards [coefficient_ae_trim b u j, hu] with p hp hq
  rw [hp]
  exact (norm_le b (u p) j).trans hq

theorem integral_coordinate_ae (b : HilbertBasis κ ℝ E)
    (J : StandardTerminalIto (C := Space ι ℝ) (E := ℝ) F μ H)
    (u : Process (E := Space ι E) F μ H) (j : κ) :
    (fun ω ↦ innerSL ℝ (b j) (HilbertTerminalIto.integral F μ H b J u ω)) =ᵐ[μ]
      J.integral (HilbertTerminalIto.coefficient F μ H b u j) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hh := (innerSL ℝ (b j)).coeFn_compLpL (HilbertTerminalIto.integral F μ H b J u)
  rw [HilbertTerminalIto.commutes] at hh
  simpa only [HilbertTerminalIto.coefficient, HilbertIsometryLift.source_coordinate] using hh.symm

theorem partial_bracket_le (b : HilbertBasis κ ℝ E) (u : Process (E := Space ι E) F μ H)
    (s : Finset κ) :
    ∀ᵐ ω ∂μ, (∑ j ∈ s, StochasticExponential.bracket F μ H
      (HilbertTerminalIto.coefficient F μ H b u j) ω) ≤ StochasticExponential.bracket F μ H u ω := by
  have hrep : ∀ᵐ p ∂energyMeasure μ H, ∀ j, HilbertTerminalIto.coefficient F μ H b u j p =
      mapCLM (innerSL ℝ (b j)) (u p) := ae_all_iff.mpr (coefficient_ae b u)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hrep
  have huI := (memLp_of_memLp_trim (predictable_le_product F) (Lp.memLp u)).norm.integrable_sq
  have hRI (j : κ) := (memLp_of_memLp_trim (predictable_le_product F)
    (Lp.memLp (HilbertTerminalIto.coefficient F μ H b u j))).norm.integrable_sq
  filter_upwards [huI.prod_left_ae, ae_all_iff.mpr (fun j ↦ (hRI j).prod_left_ae),
    Measure.ae_ae_of_ae_prod hs] with ω huω hrω heω
  change (∑ j ∈ s, (∫ r, ‖HilbertTerminalIto.coefficient F μ H b u j (r, ω)‖ ^ 2 ∂timeMeasure H)) ≤
    ∫ r, ‖u (r, ω)‖ ^ 2 ∂timeMeasure H
  rw [← integral_finsetSum _ (fun j _ ↦ hrω j)]
  apply integral_mono_ae (integrable_finsetSum _ (fun j _ ↦ hrω j)) huω
  filter_upwards [heω] with r hr
  change ∀ j, HilbertTerminalIto.coefficient F μ H b u j (r, ω) =
    mapCLM (innerSL ℝ (b j)) (u (r, ω)) at hr
  simp_rw [hr]
  exact sum_sq_le b (u (r, ω)) s

end SHEStochastic.HilbertCoefficientBounds
