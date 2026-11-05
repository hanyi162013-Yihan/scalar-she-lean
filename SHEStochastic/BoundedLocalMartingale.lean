module

public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.BoundedLocalMartingale
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

/-- For a process starting at zero, ordinary stopped martingales give
Mathlib's local-martingale predicate, including its zero-exit indicator. -/
theorem locally_of_stopped (M : ℝ≥0 → Ω → ℝ) (hzero : ∀ sample, M 0 sample = 0)
    (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : IsLocalizingSequence F τ μ)
    (hm : ∀ N, Martingale (stoppedProcess M (τ N)) F μ) :
    Locally (fun X ↦ Martingale X F μ) F M μ := by
  refine ⟨τ, hτ, fun N ↦ ?_⟩
  have he : stoppedProcess (fun t ↦ {sample | ⊥ < τ N sample}.indicator (M t)) (τ N) =
      stoppedProcess M (τ N) := by
    funext t sample
    by_cases h : ⊥ < τ N sample
    · simp only [stoppedProcess, Set.indicator_of_mem (show sample ∈ {s | ⊥ < τ N s} from h)]
    · have hb : τ N sample = ⊥ := bot_unique (le_of_not_gt h)
      simp [stoppedProcess, hb, hzero]
  rw [he]
  exact hm N

/-- A local martingale dominated on all times by one integrable random
variable is a genuine martingale. Almost-sure bounds suffice, including
bounds obtained from regularity of the actual native solution. -/
theorem martingale_of_dominated (M : ℝ≥0 → Ω → ℝ) (hadapt : StronglyAdapted F M)
    (hlocal : Locally (fun X ↦ Martingale X F μ) F M μ)
    (bound : Ω → ℝ) (hiBound : Integrable bound μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, ‖M t ω‖ ≤ bound ω) : Martingale M F μ := by
  let τ := hlocal.localSeq
  let Y (n : ℕ) := stoppedProcess (fun t ↦ {ω | ⊥ < τ n ω}.indicator (M t)) (τ n)
  have hY (n : ℕ) : Martingale (Y n) F μ := hlocal.stoppedProcess_localSeq n
  have hB (n : ℕ) (t : ℝ≥0) : ∀ᵐ ω ∂μ, ‖Y n t ω‖ ≤ bound ω :=
    hbound.mono fun ω hω ↦
      (norm_indicator_le_norm_self (M ((min (t : WithTop ℝ≥0) (τ n ω)).untopA)) ω).trans (hω _)
  have hlim (t : ℝ≥0) : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n t ω) atTop (𝓝 (M t ω)) := by
    filter_upwards [hlocal.isLocalizingSequence_localSeq.tendsto_top] with ω hω
    rw [WithTop.tendsto_nhds_top_iff] at hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω t] with n hn
    change M t ω = stoppedProcess (fun t ↦ {ω | ⊥ < τ n ω}.indicator (M t)) (τ n) t ω
    rw [stoppedProcess_eq_of_le hn.le,
      Set.indicator_of_mem (show ω ∈ {ω | ⊥ < τ n ω} from bot_lt_of_lt hn)]
  have hi (t : ℝ≥0) : Integrable (M t) μ :=
    hiBound.mono' ((hadapt t).mono (F.le t)).aestronglyMeasurable
      (hbound.mono fun ω hω ↦ hω t)
  have hI (t : ℝ≥0) (A : Set Ω) :
      Tendsto (fun n ↦ ∫ ω in A, Y n t ω ∂μ) atTop (𝓝 (∫ ω in A, M t ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence bound
      (fun n ↦ ((hY n).stronglyAdapted t |>.mono (F.le t)).aestronglyMeasurable)
      hiBound.integrableOn (fun n ↦ ae_restrict_of_ae (hB n t))
      (ae_restrict_of_ae (hlim t))
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun A _ _ ↦ (hi s).integrableOn)
  · intro A hA _
    have he (n : ℕ) : (∫ ω in A, Y n s ω ∂μ) = ∫ ω in A, Y n t ω ∂μ :=
      (hY n).setIntegral_eq hst hA
    exact tendsto_nhds_unique (hI s A) ((hI t A).congr' (Eventually.of_forall fun n ↦ (he n).symm))
  · exact (hadapt s).aestronglyMeasurable

/-- The deterministic uniformly bounded case specializes the same
almost-sure dominated argument. -/
theorem martingale (M : ℝ≥0 → Ω → ℝ) (hadapt : StronglyAdapted F M)
    (hlocal : Locally (fun X ↦ Martingale X F μ) F M μ)
    (C : ℝ) (hbound : ∀ t ω, ‖M t ω‖ ≤ C) : Martingale M F μ :=
  martingale_of_dominated μ F M hadapt hlocal (fun _ ↦ C) (integrable_const C)
    (Eventually.of_forall fun ω t ↦ hbound t ω)

end SHEStochastic.BoundedLocalMartingale
