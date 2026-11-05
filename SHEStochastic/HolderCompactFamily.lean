module

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HolderCompactFamily
open Set Metric
open scoped Topology

variable {T V : Type*} [MetricSpace T] [CompactSpace T]
  [NormedAddCommGroup V] [ProperSpace V]

/-- A uniform bound and a common positive Hölder modulus define a
compact family. This applies to scalar and finite-dimensional fields. -/
def boundedSet (R K α : ℝ) : Set (BoundedContinuousFunction T V) :=
  {f | (∀ t, ‖f t‖ ≤ R) ∧ ∀ s t, dist (f s) (f t) ≤ K * dist s t ^ α}

theorem isClosed_boundedSet (R K α : ℝ) : IsClosed (boundedSet (T := T) (V := V) R K α) := by
  have h₁ : IsClosed {f : BoundedContinuousFunction T V | ∀ t, ‖f t‖ ≤ R} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun t ↦ isClosed_le (continuous_eval_const t).norm continuous_const
  have h₂ : IsClosed {f : BoundedContinuousFunction T V |
      ∀ s t, dist (f s) (f t) ≤ K * dist s t ^ α} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s ↦ isClosed_iInter fun t ↦
      isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const
  exact h₁.inter h₂

theorem isCompact_boundedSet (R K α : ℝ) (hα : 0 < α) :
    IsCompact (boundedSet (T := T) (V := V) R K α) := by
  let S := boundedSet (T := T) (V := V) R K α
  have hmod : Filter.Tendsto (fun r : ℝ ↦ K * r ^ α) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ ↦ K * r ^ α) :=
      continuous_const.mul (Real.continuous_rpow_const hα.le)
    simpa only [Real.zero_rpow hα.ne', mul_zero] using hc.tendsto (0 : ℝ)
  have he : Equicontinuous ((↑) : S → T → V) :=
    (Metric.uniformEquicontinuous_of_continuity_modulus (fun r : ℝ ↦ K * r ^ α)
      hmod ((↑) : S → T → V) (fun s t f ↦ f.property.2 s t)).equicontinuous
  apply BoundedContinuousFunction.arzela_ascoli₂ (closedBall (0 : V) R)
    (isCompact_closedBall _ _) S (isClosed_boundedSet R K α) _ he
  intro f t hf
  simpa only [mem_closedBall, dist_zero_right] using hf.1 t

/-- The same compact set in ordinary continuous-map path space. -/
def continuousSet (R K α : ℝ) : Set C(T, V) :=
  (ContinuousMap.isometryEquivBoundedOfCompact T V).symm '' boundedSet R K α

theorem isCompact_continuousSet (R K α : ℝ) (hα : 0 < α) :
    IsCompact (continuousSet (T := T) (V := V) R K α) :=
  (isCompact_boundedSet R K α hα).image
    (ContinuousMap.isometryEquivBoundedOfCompact T V).symm.continuous

/-- A bound at one anchor suffices: the common Hölder modulus controls
the uniform norm on the compact parameter domain. -/
def anchoredSet (t₀ : T) (R K α : ℝ) : Set (BoundedContinuousFunction T V) :=
  {f | ‖f t₀‖ ≤ R ∧ ∀ s t, dist (f s) (f t) ≤ K * dist s t ^ α}

theorem isCompact_anchoredSet (t₀ : T) (R K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α) :
    IsCompact (anchoredSet (V := V) t₀ R K α) := by
  have hclosed : IsClosed (anchoredSet (V := V) t₀ R K α) := by
    have hp : IsClosed {f : BoundedContinuousFunction T V |
        ∀ s t, dist (f s) (f t) ≤ K * dist s t ^ α} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun s ↦ isClosed_iInter fun t ↦
        isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const
    exact (isClosed_le (continuous_eval_const t₀).norm continuous_const).inter hp
  apply (isCompact_boundedSet (T := T) (V := V)
    (R + K * (diam (Set.univ : Set T)) ^ α) K α hα).of_isClosed_subset hclosed
  intro f hf
  refine ⟨?_, hf.2⟩
  intro t
  calc
    ‖f t‖ = ‖(f t - f t₀) + f t₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖f t - f t₀‖ + ‖f t₀‖ := norm_add_le _ _
    _ = dist (f t) (f t₀) + ‖f t₀‖ := by rw [dist_eq_norm]
    _ ≤ K * dist t t₀ ^ α + R := add_le_add (hf.2 t t₀) hf.1
    _ ≤ R + K * (diam (Set.univ : Set T)) ^ α := by
      have hd : dist t t₀ ≤ diam (Set.univ : Set T) :=
        dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ t) (mem_univ t₀)
      nlinarith [mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg hd hα.le) hK]

end SHEStochastic.HolderCompactFamily
