module

public import SHE.ApproximationCells

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ContinuousPredictable
open MeasureTheory Set Filter ApproximationCells
open scoped Topology NNReal

def leftPoint (n : ℕ) (t : ℝ≥0) : ℝ≥0 := point n (index n t-1)

theorem leftPoint_zero (n : ℕ) : leftPoint n 0=0 := by
  apply Subtype.ext
  change ApproximationClock.delta n * ((⌈(0:ℝ)/ApproximationClock.delta n⌉₊-1:ℕ):ℝ)=0
  simp

theorem leftPoint_tendsto (t : ℝ≥0) : Tendsto (fun n => leftPoint n t) atTop (𝓝 t) := by
  by_cases ht : t=0
  · subst t
    simpa only [leftPoint_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0)) atTop (𝓝 0))
  · have htpos : 0 < t := lt_of_le_of_ne zero_le (Ne.symm ht)
    apply NNReal.tendsto_coe.mp
    have he : (fun n => (leftPoint n t:ℝ))=fun n => ApproximationClock.left n (t:ℝ) := by
      funext n
      exact (left_eq_point n htpos).symm
    rw [he]
    exact ApproximationClock.left_tendsto t.2

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (u : ℝ≥0 → Ω → E)

def approximation (n : ℕ) (p : ℝ≥0 × Ω) : E := u (leftPoint n p.1) p.2

theorem approximation_predictable (ha : StronglyAdapted 𝓕 u) (n : ℕ) :
    StronglyMeasurable[𝓕.predictable] (approximation u n) := by
  apply stronglyMeasurable_iff_measurable.mpr
  intro B hB
  have he : approximation u n ⁻¹' B =
      ({0} ×ˢ (u 0 ⁻¹' B)) ∪
        ⋃ k : ℕ, Ioc (point n k) (point n (k+1)) ×ˢ (u (point n k) ⁻¹' B) := by
    ext p
    rcases p with ⟨t,ω⟩
    by_cases ht : t=0
    · subst t
      have hcell (k : ℕ) : (0:ℝ≥0) ∉ Ioc (point n k) (point n (k+1)) := by
        intro hh
        exact (not_lt_of_ge (show (0:ℝ≥0) ≤ point n k from zero_le)) hh.1
      simp [approximation,leftPoint_zero,hcell]
    · have htpos : 0 < t := lt_of_le_of_ne zero_le (Ne.symm ht)
      have hi : 1 ≤ index n t := (Finset.mem_Icc.mp (index_mem n htpos le_rfl)).1
      constructor
      · intro hh
        apply Or.inr
        apply mem_iUnion.mpr
        refine ⟨index n t-1,?_,hh⟩
        have hik : index n t-1+1=index n t := by omega
        have hsub : index n t-1+1-1=index n t-1 := by omega
        have hc := (cell_iff n (index n t-1+1) (by omega) t).mpr hik.symm
        simpa only [hsub] using hc
      · intro hh
        rcases hh with hh | hh
        · exact (ht (by simpa using hh.1)).elim
        · rcases mem_iUnion.mp hh with ⟨k,hk,hval⟩
          have heq : index n t=k+1 := (cell_iff n (k+1) (by omega) t).mp (by simpa using hk)
          change u (point n (index n t-1)) ω ∈ B
          rw [heq,Nat.add_sub_cancel]
          exact hval
  rw [he]
  apply MeasurableSet.union
  · exact measurableSet_predictable_singleton_bot_prod ((ha 0).measurable hB)
  · apply MeasurableSet.iUnion
    intro k
    exact measurableSet_predictable_Ioc_prod _ _ ((ha (point n k)).measurable hB)

/-- Continuous adapted paths are genuinely predictable. The proof uses
left-known dyadic cells and their pointwise limit, rather than assuming
joint predictability as a further stochastic input. -/
theorem stronglyMeasurable (ha : StronglyAdapted 𝓕 u)
    (hc : ∀ ω, Continuous (fun t => u t ω)) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry u) := by
  apply stronglyMeasurable_of_tendsto atTop (approximation_predictable 𝓕 u ha)
  apply tendsto_pi_nhds.mpr
  intro p
  exact (hc p.2).continuousAt.tendsto.comp (leftPoint_tendsto p.1)

theorem isStronglyPredictable (ha : StronglyAdapted 𝓕 u)
    (hc : ∀ ω, Continuous (fun t => u t ω)) : IsStronglyPredictable 𝓕 u :=
  stronglyMeasurable 𝓕 u ha hc

end SHE.ContinuousPredictable
