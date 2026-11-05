module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.LocalizationLawLimit
open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
  {μ : Measure Ω} {ν : Measure Ω'}

/-- An original path and its stopped path differ only on the exit
event. This estimate applies to every measurable path event directly. -/
theorem law_le_add_exit (U V : Ω → X) (hU : Measurable U) (hV : Measurable V)
    (bad : Set Ω) (hgood : ∀ ω ∉ bad, U ω = V ω)
    (A : Set X) (hA : MeasurableSet A) : μ.map U A ≤ μ.map V A + μ bad := by
  rw [Measure.map_apply hU hA, Measure.map_apply hV hA]
  refine (measure_mono (show U ⁻¹' A ⊆ (V ⁻¹' A) ∪ bad from ?_)).trans (measure_union_le _ _)
  intro ω hω
  by_cases hb : ω ∈ bad
  · exact Or.inr hb
  · apply Or.inl
    change V ω ∈ A
    rw [← hgood ω hb]
    exact hω

theorem law_le_of_localized (U : Ω → X) (V : Ω' → X)
    (hU : Measurable U) (hV : Measurable V)
    (Ucut : ℕ → Ω → X) (Vcut : ℕ → Ω' → X)
    (hUc : ∀ n, Measurable (Ucut n)) (hVc : ∀ n, Measurable (Vcut n))
    (bad : ℕ → Set Ω) (bad' : ℕ → Set Ω')
    (hgood : ∀ n ω, ω ∉ bad n → U ω = Ucut n ω)
    (hgood' : ∀ n ω, ω ∉ bad' n → V ω = Vcut n ω)
    (same : ∀ n, μ.map (Ucut n) = ν.map (Vcut n))
    (hexit : Tendsto (fun n ↦ μ (bad n)) atTop (𝓝 0))
    (hexit' : Tendsto (fun n ↦ ν (bad' n)) atTop (𝓝 0)) : μ.map U ≤ ν.map V := by
  apply Measure.le_iff.mpr
  intro A hA
  have hb (n : ℕ) : μ.map U A ≤ ν.map V A + μ (bad n) + ν (bad' n) := by
    calc
      _ ≤ μ.map (Ucut n) A + μ (bad n) := law_le_add_exit U (Ucut n) hU (hUc n) (bad n) (hgood n) A hA
      _ = ν.map (Vcut n) A + μ (bad n) := congrArg (fun m : Measure X ↦ m A + μ (bad n)) (same n)
      _ ≤ (ν.map V A + ν (bad' n)) + μ (bad n) := add_le_add_left
        (law_le_add_exit (Vcut n) V (hVc n) hV (bad' n)
          (fun ω hω ↦ (hgood' n ω hω).symm) A hA) _
      _ = _ := by ac_rfl
  have ht := ((tendsto_const_nhds (x := ν.map V A)).add hexit).add hexit'
  simpa only [add_zero] using ge_of_tendsto' ht hb

/-- Equality of stopped path laws and vanishing exit probabilities give
equality on the full original path space, even on different sample spaces.
No coupling, moment estimate or existence premise is hidden here. -/
theorem laws_eq_of_localized (U : Ω → X) (V : Ω' → X)
    (hU : Measurable U) (hV : Measurable V)
    (Ucut : ℕ → Ω → X) (Vcut : ℕ → Ω' → X)
    (hUc : ∀ n, Measurable (Ucut n)) (hVc : ∀ n, Measurable (Vcut n))
    (bad : ℕ → Set Ω) (bad' : ℕ → Set Ω')
    (hgood : ∀ n ω, ω ∉ bad n → U ω = Ucut n ω)
    (hgood' : ∀ n ω, ω ∉ bad' n → V ω = Vcut n ω)
    (same : ∀ n, μ.map (Ucut n) = ν.map (Vcut n))
    (hexit : Tendsto (fun n ↦ μ (bad n)) atTop (𝓝 0))
    (hexit' : Tendsto (fun n ↦ ν (bad' n)) atTop (𝓝 0)) : μ.map U = ν.map V :=
  le_antisymm (law_le_of_localized U V hU hV Ucut Vcut hUc hVc bad bad' hgood hgood' same hexit hexit')
    (law_le_of_localized V U hV hU Vcut Ucut hVc hUc bad' bad hgood' hgood
      (fun n ↦ (same n).symm) hexit' hexit)

end SHEStochastic.LocalizationLawLimit
