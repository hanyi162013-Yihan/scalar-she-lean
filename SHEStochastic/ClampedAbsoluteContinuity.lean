module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.ClampedAbsoluteContinuity
open Set

/-- Projection to a closed real interval, with constant extensions. -/
def clamp (a b r : ℝ) : ℝ := max a (min b r)

theorem monotone (a b : ℝ) : Monotone (clamp a b) := monotone_const.max (monotone_const.min monotone_id)

theorem lipschitz (a b : ℝ) : LipschitzWith 1 (clamp a b) :=
  (LipschitzWith.id.const_min b).const_max a

theorem mem {a b : ℝ} (hab : a ≤ b) (r : ℝ) : clamp a b r ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem of_le_left {a b r : ℝ} (hab : a ≤ b) (hr : r ≤ a) : clamp a b r = a := by
  rw [clamp, min_eq_right (hr.trans hab), max_eq_left hr]

theorem of_right_le {a b r : ℝ} (hab : a ≤ b) (hr : b ≤ r) : clamp a b r = b := by
  rw [clamp, min_eq_left hr, max_eq_right hab]

theorem of_mem {a b r : ℝ} (hr : r ∈ Icc a b) : clamp a b r = r := by
  rw [clamp, min_eq_right hr.2, max_eq_right hr.1]

theorem cell_subset {a b : ℝ} (hab : a ≤ b) (r s : ℝ) (hrs : r ≤ s) :
    Ioc (clamp a b r) (clamp a b s) ⊆ Ioc r s := by
  intro z hz
  have hrb : r ≤ b := by
    by_contra h
    have hr : clamp a b r = b := by simp [clamp, min_eq_left (le_of_not_ge h), max_eq_right hab]
    have hs : clamp a b s = b := by simp [clamp, min_eq_left ((le_of_not_ge h).trans hrs), max_eq_right hab]
    rw [hr, hs] at hz
    exact (not_lt_of_ge hz.2) hz.1
  have has : a ≤ s := by
    by_contra h
    have hs : clamp a b s = a := max_eq_left ((min_le_right b s).trans (le_of_not_ge h))
    have hr : clamp a b r = a := max_eq_left ((min_le_right b r).trans (hrs.trans (le_of_not_ge h)))
    rw [hr, hs] at hz
    exact (not_lt_of_ge hz.2) hz.1
  refine ⟨lt_of_le_of_lt ?_ hz.1, hz.2.trans ?_⟩
  · simpa only [clamp, min_eq_right hrb] using le_max_right a r
  · exact max_le has (min_le_right _ _)

theorem ucell_subset {a b : ℝ} (hab : a ≤ b) (r s : ℝ) :
    uIoc (clamp a b r) (clamp a b s) ⊆ uIoc r s := by
  rcases le_total r s with hrs | hsr
  · rw [uIoc_of_le hrs, uIoc_of_le (monotone a b hrs)]
    exact cell_subset hab r s hrs
  · rw [uIoc_comm (clamp a b r), uIoc_comm r]
    rw [uIoc_of_le hsr, uIoc_of_le (monotone a b hsr)]
    exact cell_subset hab s r hsr

/-- Constant extension outside the original interval preserves absolute
continuity. Clipping shrinks disjoint time cells and contracts their
total length, so the original epsilon-delta estimate applies unchanged. -/
theorem extension {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) (c d : ℝ) :
    AbsolutelyContinuousOnInterval (fun r ↦ f (clamp a b r)) c d := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro V hV hlen
  let W : ℕ × (ℕ → ℝ × ℝ) := (V.1, fun i ↦ (clamp a b (V.2 i).1, clamp a b (V.2 i).2))
  have hW : W ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    constructor
    · intro i hi
      rw [uIcc_of_le hab]
      exact ⟨mem hab _, mem hab _⟩
    · intro i hi j hj hij
      exact (hV.2 hi hj hij).mono (ucell_subset hab _ _) (ucell_subset hab _ _)
  have hwlen : (∑ i ∈ Finset.range W.1, dist (W.2 i).1 (W.2 i).2) < δ := by
    refine (Finset.sum_le_sum (fun i hi ↦ ?_)).trans_lt hlen
    simpa only [NNReal.coe_one, one_mul] using (lipschitz a b).dist_le_mul (V.2 i).1 (V.2 i).2
  exact hbound W hW hwlen

end SHEStochastic.ClampedAbsoluteContinuity
