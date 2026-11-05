module

public import SHEStochastic.HolderCompactFamily
public import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.KolmogorovFieldControl
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

variable {T V : Type*} [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
  [NormedAddCommGroup V] [ProperSpace V]
  (D : Set T) (p : ℝ) (α : ℝ≥0)

/-- The countable Hölder control appearing in the public quantitative
Chentsov theorem, as an explicit Borel functional of a continuous field. -/
def control (f : C(T, V)) : ℝ≥0∞ :=
  ⨆ (s : (D ∩ Set.univ : Set T)) (t : (D ∩ Set.univ : Set T)),
    edist (f s) (f t) ^ p / edist s t ^ ((α : ℝ) * p)

theorem measurable_control (hD : D.Countable) : Measurable (control (V := V) D p α) := by
  letI : Countable D := hD
  letI : Countable (D ∩ Set.univ : Set T) := hD.mono inter_subset_left
  apply Measurable.iSup
  intro s
  apply Measurable.iSup
  intro t
  have hs : Continuous (fun f : C(T, V) ↦ f (s : T)) := continuous_eval_const _
  have ht : Continuous (fun f : C(T, V) ↦ f (t : T)) := continuous_eval_const _
  exact ((hs.edist ht).measurable.pow_const p).div measurable_const

/-- A finite countable control gives the same quantitative Hölder bound
on the whole compact parameter domain, by continuity and density. -/
theorem distance_bound (hD : Dense D) {c : ℝ≥0∞} {d : ℝ}
    (hT : HasCoveringExponent (Set.univ : Set T) c d) (hp : 0 < p) (hα : 0 < α)
    (f : C(T, V)) (hfinite : control D p α f < ⊤) (s t : T) :
    dist (f s) (f t) ≤ ((control D p α f ^ p⁻¹).toNNReal : ℝ) * dist s t ^ (α : ℝ) := by
  let X : T → Unit → V := fun u _ ↦ f u
  have hmem : () ∈ holderSet X D p α Set.univ := by
    simp only [holderSet, mem_setOf_eq, inter_univ]
    refine ⟨?_, ?_⟩
    · exact hfinite
    intro u v huv
    have he : (u : T) = (v : T) := edist_eq_zero.mp huv
    change edist (f u) (f v) = 0
    rw [he, edist_self]
  have hh := holderOnWith_of_mem_holderSet hT hp hα hmem
  let K : ℝ≥0 := (control D p α f ^ p⁻¹).toNNReal
  have hsub : D ×ˢ D ⊆ {z : T × T | dist (f z.1) (f z.2) ≤ K * dist z.1 z.2 ^ (α : ℝ)} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hz := hh.dist_le (x := (⟨u, hu⟩ : D)) (y := (⟨v, hv⟩ : D)) (mem_univ _) (mem_univ _)
    convert hz using 1 <;> rfl
  have hc : IsClosed {z : T × T | dist (f z.1) (f z.2) ≤ K * dist z.1 z.2 ^ (α : ℝ)} :=
    isClosed_le ((f.continuous.comp continuous_fst).dist (f.continuous.comp continuous_snd))
      (continuous_const.mul
        ((continuous_fst.dist continuous_snd).rpow_const (fun _ ↦ Or.inr α.property)))
  exact (closure_minimal hsub hc) ((hD.prod hD) (s, t))

/-- A fixed level of the control gives a common Hölder constant. -/
theorem distance_bound_of_le (hD : Dense D) {c : ℝ≥0∞} {d : ℝ}
    (hT : HasCoveringExponent (Set.univ : Set T) c d) (hp : 0 < p) (hα : 0 < α)
    (f : C(T, V)) (R : ℝ≥0) (hbound : control D p α f ≤ R) (s t : T) :
    dist (f s) (f t) ≤ (((R : ℝ≥0∞) ^ p⁻¹).toNNReal : ℝ) * dist s t ^ (α : ℝ) := by
  have hfinite : control D p α f < ⊤ := hbound.trans_lt ENNReal.coe_lt_top
  have hr : (R : ℝ≥0∞) ^ p⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le) ENNReal.coe_ne_top
  have hk : (control D p α f ^ p⁻¹).toNNReal ≤ ((R : ℝ≥0∞) ^ p⁻¹).toNNReal :=
    ENNReal.toNNReal_mono hr (ENNReal.rpow_le_rpow hbound (inv_nonneg.mpr hp.le))
  exact (distance_bound D p α hD hT hp hα f hfinite s t).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Real.rpow_nonneg dist_nonneg _))

end SHEStochastic.KolmogorovFieldControl
