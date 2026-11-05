/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Adapted

/-!
Compatibility subset of BrownianMotion at 729ee65f8fa6c36d3521051b498d6918b4b7ce6d.
Brownian finite-dimensional laws are already in the pinned mathlib. Only the
filtered Brownian definition and its two existing proofs are needed here;
no Brownian-construction theorem is replaced by an assumption.
-/

@[expose] public section

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace ProbabilityTheory
variable {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- A pre-Brownian motion `X` is **filtered** with respect to a filtration `𝓕` if it is adapted
to `𝓕` and the increments of `X` after time `t` are independent of `𝓕 t` -/
class IsFilteredPreBrownian (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop
  extends IsPreBrownianReal X P where
    stronglyAdapted : StronglyAdapted 𝓕 X
    indep : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (X t - X s) inferInstance) (𝓕 s) P

lemma IsPreBrownianReal.isFilteredPreBrownian (h : IsPreBrownianReal X P)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    IsFilteredPreBrownian X (natural X (fun t ↦ (hX t).stronglyMeasurable)) P where
  stronglyAdapted := stronglyAdapted_natural (fun t ↦ (hX t).stronglyMeasurable)
  indep s t hst := by
    have h := (IndepFun_iff_Indep _ _ _).1 (h.indepFun_shift s)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
    · have hX : X t - X s = (fun f ↦ f (t - s)) ∘ (fun ω u ↦ (X (s + u) ω - X s ω)) := by
        funext; simp [add_tsub_cancel_of_le, hst]
      rw [hX, ←comap_comp]; apply comap_mono (Measurable.comap_le _); fun_prop
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have hX : (X u) = ((fun f ↦ f ⟨u,hu⟩) ∘ (fun ω (t : Set.Iic s) ↦ X t ω)) := by
        funext; simp
      rw [hX, ←comap_comp]; apply comap_mono (Measurable.comap_le _); fun_prop
  hasLaw := h.hasLaw

lemma IsPreBrownianReal.isMartingale (X : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] [hX : IsFilteredPreBrownian X 𝓕 P] : Martingale X 𝓕 P := by
  refine ⟨hX.stronglyAdapted, fun s t hst => ?_⟩
  have hM := fun t ↦ ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_no_cond : P[X t - X s | 𝓕 s] =ᵐ[P] fun _ ↦ P[X t - X s] := by
    refine condExp_indep_eq ?_ (𝓕.le s) ?_ (hX.indep s t hst)
    · exact Measurable.comap_le (Measurable.sub (hM t) (hM s))
    · exact (comap_measurable (X t - X s)).stronglyMeasurable
  have h_integral_zero : P[X t - X s] = 0 := calc
    P[X t - X s] = P[X t] - P[X s] := integral_sub (hX.integrable_eval t) (hX.integrable_eval s)
    _ = ↑0 := by simp [hX.integral_eval]
  calc
    _ = P[(X t - X s) + X s | 𝓕 s] := by simp
    _ =ᵐ[P] P[X t - X s | 𝓕 s] + P[X s | 𝓕 s] := condExp_add ((Integrable.sub
      (hX.integrable_eval t) (hX.integrable_eval s))) (hX.integrable_eval s) (𝓕 s)
    _ = P[X t - X s | 𝓕 s] + X s := by
      rw [condExp_of_stronglyMeasurable (𝓕.le s) (hX.stronglyAdapted s) (hX.integrable_eval s)]
    _ =ᵐ[P] (fun _ ↦ P[X t - X s]) + X s := by filter_upwards [h_no_cond] with ω hω; simp [hω]
    _ = X s := by aesop


end ProbabilityTheory
