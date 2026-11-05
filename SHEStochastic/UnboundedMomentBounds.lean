module

public import SHE.Feedback
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.UnboundedMomentBounds
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Uniform absorption of the stopped sublinear moment estimate. The
existing feedback theorem supplies the nonlinear branch of the bound. -/
theorem absorb {x A B β : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hβ : β < 1) (h : x ≤ A + B * x ^ β) :
    x ≤ max (2 * A) ((2 * B) ^ (1 / (1 - β))) := by
  by_cases hsmall : x ≤ 2 * A
  · exact hsmall.trans (le_max_left _ _)
  · have hlarge : x ≤ (2 * B) * x ^ β := by linarith
    exact (SHE.sublinear_bound hx (by positivity) hβ hlarge).trans (le_max_right _ _)

/-- A finite real-valued remainder supremum has vanishing tails.
For uniqueness alone, no quantitative moment estimate is needed here. -/
theorem tails_vanish {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℝ) (hD : Measurable D) :
    Tendsto (fun n : ℕ ↦ μ {ω | (n : ℝ) ≤ D ω}) atTop (𝓝 0) := by
  let S (n : ℕ) := {ω | (n : ℝ) ≤ D ω}
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hD
  have hm : Antitone S := by
    intro n m hnm ω hω
    exact (show (n : ℝ) ≤ m by exact_mod_cast hnm).trans hω
  have he : (⋂ n, S n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hω
    obtain ⟨n, hn⟩ := exists_nat_gt (D ω)
    exact (not_le_of_gt hn) (hω n)
  have hh := tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ (hS n).nullMeasurableSet)
    hm ⟨0, measure_ne_top μ _⟩
  simpa only [Function.comp_def, he, measure_empty] using hh

theorem exit_vanishes {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℝ) (hD : Measurable D) (bad : ℕ → Set Ω)
    (hbad : ∀ n, bad n ⊆ {ω | (n : ℝ) ≤ D ω}) :
    Tendsto (fun n ↦ μ (bad n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tails_vanish μ D hD)
    (fun _ ↦ zero_le) (fun n ↦ measure_mono (hbad n))

end SHEStochastic.UnboundedMomentBounds
