module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.TightnessByLocalization
open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- Tight localized path laws and a uniform vanishing exit probability
give tightness of the original path laws. The original coupling and
each probability space are retained; no convergence coupling is assumed. -/
theorem tight {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    (μ : ∀ m,Measure (Ω m)) (X : ∀ m,Ω m → E) (hX : ∀ m,Measurable (X m))
    (Y : ∀ K m,Ω m → E) (hY : ∀ K m,Measurable (Y K m))
    (hTight : ∀ K,IsTightMeasureSet (Set.range (fun m => (μ m).map (Y K m))))
    (error : ℕ → ℝ≥0∞) (he : Tendsto error atTop (𝓝 0))
    (hbad : ∀ K m,(μ m) {ω | X m ω≠Y K m ω}≤error K) :
    IsTightMeasureSet (Set.range (fun m => (μ m).map (X m))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases htop : ε=⊤
  · subst ε
    exact ⟨∅,isCompact_empty,fun _ _ => le_top⟩
  have hhalf : (0 : ℝ≥0∞)<ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨K,hK⟩ := ((tendsto_order.mp he).2 (ε/2) hhalf).exists
  obtain ⟨C,hC,hBound⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hTight K)) (ε/2) hhalf
  refine ⟨C,hC,?_⟩
  rintro _ ⟨m,rfl⟩
  rw [Measure.map_apply (hX m) hC.isClosed.measurableSet.compl]
  calc
    _ ≤ (μ m) ({ω | Y K m ω∉C}∪{ω | X m ω≠Y K m ω}) := by
      apply measure_mono
      intro ω hω
      by_cases hy : Y K m ω∈C
      · right
        intro heq
        exact hω (heq.symm ▸ hy)
      · exact Or.inl hy
    _ ≤ (μ m) {ω | Y K m ω∉C}+(μ m) {ω | X m ω≠Y K m ω} := measure_union_le _ _
    _ = ((μ m).map (Y K m)) Cᶜ+(μ m) {ω | X m ω≠Y K m ω} := by
      rw [Measure.map_apply (hY K m) hC.isClosed.measurableSet.compl]
      rfl
    _ ≤ ε/2+error K := add_le_add (hBound _ (mem_range_self m)) (hbad K m)
    _ ≤ ε/2+ε/2 := add_le_add le_rfl hK.le
    _ = ε := ENNReal.add_halves ε

end SHEStochastic.TightnessByLocalization
