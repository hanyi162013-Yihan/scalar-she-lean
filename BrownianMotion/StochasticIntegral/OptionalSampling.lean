/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import BrownianMotion.Auxiliary.Adapted
public import BrownianMotion.Auxiliary.StoppedValue
public import BrownianMotion.StochasticIntegral.ApproxSeq
public import Mathlib.Probability.Martingale.Centering

@[expose] public section

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology

namespace MeasureTheory

namespace Martingale

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [OrderBot ι] [SecondCountableTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → E} {τ σ : Ω → WithTop ι} {n : ι}

lemma condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω)) {i : ι} (hτ_le : ∀ x, τ x ≤ i)
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτ_countable_range : (Set.range τ).Countable) :
    μ[stoppedValue X τ|hσ.measurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue X τ := by
  borelize ι
  rw [ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))]
  refine (condExp_indicator
    (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
    (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have h_int :
      Integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ :=
    Integrable.indicator
      (h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range)
      <| hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
  have h_meas : AEStronglyMeasurable[hσ.measurableSpace]
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) μ := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
      (hτ.measurableSet_le_stopping_time hσ) ?_ ?_ ?_
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
      exact ht.2
    · exact (stronglyMeasurable_stoppedValue
        (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC) hRC
        hτ).indicator (hτ.measurableSet_le_stopping_time hσ)
    · intro x hx
      simp only [hx, Set.indicator_of_notMem, not_false_iff]
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le h_meas h_int

lemma stoppedValue_min_ae_eq_condExp_of_countable_range
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable) :
    (stoppedValue X fun x ↦ min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  borelize ι
  refine
    (h.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ
      (hσ.min hτ) (fun x ↦ min_le_right _ _) hτ_le hτ_countable_range ?_).trans ?_
  · exact (hτ_countable_range.union hσ_countable_range).mono <| by grind
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · suffices μ[stoppedValue X τ|(hσ.min hτ).measurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
        μ[stoppedValue X τ|hσ.measurableSpace] by
      rw [ae_restrict_iff' (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
      rw [Filter.EventuallyEq, ae_restrict_iff'] at this
      swap; · exact hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ)
      filter_upwards [this] with x hx hx_mem
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx_mem
      exact hx hx_mem.le
    apply Filter.EventuallyEq.trans _ ((condExp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stoppedValue X τ
    · rw [IsStoppingTime.measurableSpace_min hσ hτ,
        IsStoppingTime.measurableSpace_min hτ hσ, inf_comm]
    · have h1 : μ[stoppedValue X τ|hτ.measurableSpace] = stoppedValue X τ := by
        apply condExp_of_stronglyMeasurable hτ.measurableSpace_le
        · exact (stronglyMeasurable_stoppedValue
            (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC) hRC
            hτ)
        · exact h.integrable_stoppedValue_of_countable_range τ hτ hτ_le hτ_countable_range
      rw [h1]
      exact (h.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range hRC hτ_le
        hτ hσ hτ_countable_range).symm

/-- **Optional sampling theorem** for general time indices
(assuming existence of `DiscreteApproxSequence`). -/
theorem stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    (τn : DiscreteApproxSequence 𝓕 τ μ) (σn : DiscreteApproxSequence 𝓕 σ μ) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] := by
  borelize ι
  set τn' := (discreteApproxSequence_of 𝓕 hτ_le τn).inf σn
  have hint (m : ℕ) : stoppedValue X (τn' m) =ᵐ[μ]
      μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace] := by
    refine EventuallyEq.trans (Eq.eventuallyEq ?_)
      (h.stoppedValue_min_ae_eq_condExp_of_countable_range hRC
        ((discreteApproxSequence_of 𝓕 hτ_le τn).isStoppingTime m)
        (σn.isStoppingTime m) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ _) (σn.countable m))
    congr 1; ext ω; rw [min_comm]; rfl
  have hintgbl : Integrable (stoppedValue X τ) μ :=
    integrable_stoppedValue_of_discreteApproxSequence' h hRC hτ_le τn
  refine ae_eq_condExp_of_forall_setIntegral_eq _ hintgbl ?_ ?_
    ((stronglyMeasurable_stoppedValue
        (h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC) hRC
        (hτ.min hσ)).aestronglyMeasurable.mono ((hτ.min hσ).measurableSpace_mono hσ <|
          fun ω ↦ min_le_right _ _))
  · exact fun s hs _ ↦ (integrable_stoppedValue_of_discreteApproxSequence' h hRC
      (fun _ ↦ min_le_of_left_le <| hτ_le _) <| τn.inf σn).integrableOn
  rintro s hs -
  have : (fun m ↦ ∫ ω in s, stoppedValue X (τn' m) ω ∂μ) =
    fun m ↦ ∫ ω in s, stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) ω ∂μ := by
    ext m
    rw [setIntegral_congr_ae (g := μ[stoppedValue X (discreteApproxSequence_of 𝓕 hτ_le τn m) |
        (σn.isStoppingTime m).measurableSpace]) (hσ.measurableSpace_le _ hs)
        (by filter_upwards [hint m] with ω hω _ using hω)]
    exact setIntegral_condExp _
      (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))
      (hσ.measurableSpace_mono (σn.isStoppingTime m) (σn.le m) _ hs)
  refine tendsto_nhds_unique (f := (fun m ↦ ∫ (ω : Ω) in s, stoppedValue X (τn' m) ω ∂μ))
    (l := atTop) ?_ (this ▸ ?_)
  · refine tendsto_setIntegral_of_L1' _ ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence_of_le h hRC τn'
        (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le)) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
      (DiscreteApproxSequence.isStoppingTime _ _)
      (τn.discreteApproxSequence_of_le_inf_le_of_left σn hτ_le m)
      (DiscreteApproxSequence.countable _ m))⟩
  · refine tendsto_setIntegral_of_L1' _ ?_
      (tendsto_eLpNorm_stoppedValue_of_discreteApproxSequence h hRC hτ_le τn) _
    rw [eventually_atTop]
    exact ⟨0, fun m _ ↦ (h.integrable_stoppedValue_of_countable_range _
        (DiscreteApproxSequence.isStoppingTime _ _) (discreteApproxSequence_of_le hτ_le τn m)
        (DiscreteApproxSequence.countable _ m))⟩

-- TODO: change name of `stoppedValue_min_ae_eq_condExp` in mathlib and remove the prime here
/-- **Optional sampling theorem** for approximable time indices. -/
theorem stoppedValue_min_ae_eq_condExp'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
    (stoppedValue X fun x ↦ min (τ x) (σ x)) =ᵐ[μ] μ[stoppedValue X τ|hσ.measurableSpace] :=
  stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC hτ hσ hτ_le
    (hτ.discreteApproxSequence μ) (hσ.discreteApproxSequence μ)

lemma stoppedValue_ae_eq_condExp_of_le_const'
    [Approximable 𝓕 μ] (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) :
    stoppedValue X τ =ᵐ[μ] μ[X n|hτ.measurableSpace] := by
  convert stoppedValue_min_ae_eq_condExp_of_discreteApproxSequence h hRC
    (isStoppingTime_const 𝓕 n) hτ (fun _ ↦ le_rfl) (discreteApproxSequence_const 𝓕 n)
      (hτ.discreteApproxSequence μ) using 2
  · ext ω
    rw [eq_comm, min_eq_right_iff]
    exact hτ_le ω
  · rfl

theorem condExp_stoppedValue_ae_eq_stoppedProcess [Approximable 𝓕 μ] {n : ι}
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) (hτ_le : ∀ x, τ x ≤ n) (i : ι) :
    μ[stoppedValue X τ|𝓕 i] =ᵐ[μ] stoppedProcess X τ i := by
  simp_rw [stoppedProcess_eq_stoppedValue, min_comm]
  exact EventuallyEq.trans (Eq.eventuallyEq <| by simp)
    (stoppedValue_min_ae_eq_condExp' h hRC hτ (isStoppingTime_const 𝓕 i) hτ_le).symm

lemma stoppedProcess [Approximable 𝓕 μ] [PseudoMetrizableSpace ι]
    (h : Martingale X 𝓕 μ) (hRC : ∀ ω, IsRightContinuous (X · ω)) (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (stoppedProcess X τ) 𝓕 μ := by
  borelize ι
  constructor
  · exact fun t ↦
      h.stronglyAdapted.isStronglyProgressive_of_rightContinuous hRC |>.stoppedProcess hτ
        |>.stronglyAdapted t
  intro s t hst
  nth_rw 1 [stoppedProcess_eq_stoppedValue]
  grw [condExp_stoppedValue_ae_eq_stoppedProcess h hRC ((isStoppingTime_const 𝓕 t).min hτ) (n := t)]
  · apply ae_of_all
    simp only [MeasureTheory.stoppedProcess]
    intro ω
    rw [min_left_comm, min_eq_right]
    grw [min_le_left]
    simpa
  simp

end Martingale

end MeasureTheory
