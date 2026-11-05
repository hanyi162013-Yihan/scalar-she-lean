module

public import SHEStochastic.FiniteScalarIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The increment properties used by the public elementary-martingale
proof. This intermediate interface is proved for the clipped native noise;
it does not assume a global-time Brownian extension. -/
class IndependentL2Driver {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) : Prop where
  adapted : StronglyAdapted F B
  eval_memLp : ∀ t, MemLp (B t) 2 μ
  increment_memLp : ∀ s t, s ≤ t → MemLp (fun ω ↦ B t ω - B s ω) 2 μ
  independent : ∀ s t, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) μ
  centered_increment : ∀ s t, s ≤ t → ∫ ω, B t ω - B s ω ∂μ = 0

namespace FiniteScalarIto
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : Coordinates F μ H ι)

def clipped (i : ι) (t : ℝ≥0) (ω : Ω) : ℝ := P.W i (min t H) ω

theorem clipped_continuous (Q : Family F μ H ι) (i : ι) (ω : Ω) :
    Continuous (fun t ↦ clipped Q.toCoordinates i t ω) :=
  (Q.continuous i ω).comp (continuous_id.min continuous_const)

theorem clipped_increment_law (i : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun ω ↦ clipped P i t ω - clipped P i s ω)
      (gaussianReal 0 (min t H - min s H)) μ :=
  BrownianCoordinates.increment_law F μ H P.W P.law i (min s H) (min t H)
    (min_le_min hst le_rfl) (min_le_right t H)

/-- Freeze the given coordinate after H. Its increments still have the
required full-filtration independence; increments starting after H vanish. -/
instance clipped_driver (i : ι) : IndependentL2Driver (clipped P i) F μ where
  adapted t := ((P.adapted i (min t H)).mono (F.mono (min_le_left t H)) le_rfl).stronglyMeasurable
  eval_memLp t := BrownianCoordinates.memLp_eval F μ H P.W P.law i (min t H) (min_le_right t H) 2 (by simp)
  increment_memLp s t hst := (clipped_increment_law P i s t hst).memLp (memLp_id_gaussianReal' 2 (by simp))
  independent s t hst := by
    by_cases hs : s ≤ H
    · change Indep (MeasurableSpace.comap
        (fun ω ↦ P.W i (min t H) ω - P.W i (min s H) ω) inferInstance) (F s) μ
      rw [min_eq_left hs]
      exact BrownianCoordinates.independent_increment F μ H P.W P.law i s (min t H)
        (le_min hst hs) (min_le_right t H)
    · have hHs : H ≤ s := (lt_of_not_ge hs).le
      have hHt : H ≤ t := hHs.trans hst
      simp only [clipped, min_eq_right hHs, min_eq_right hHt, sub_self, MeasurableSpace.comap_const]
      exact indep_bot_left (F s)
  centered_increment s t hst := by
    have he := (clipped_increment_law P i s t hst).integral_eq
    rwa [integral_id_gaussianReal] at he

end FiniteScalarIto

namespace IndependentL2Driver
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  [D : IndependentL2Driver B F μ]
include D

theorem adapted_indepFun_increment {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) :
    IndepFun φ (fun ω ↦ B t ω - B s ω) μ := by
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le_left (D.independent s t hst).symm (Measurable.comap_le hφ)

theorem integral_adapted_mul_increment {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) :
    ∫ ω, φ ω * (B t ω - B s ω) ∂μ = 0 := by
  have hi := adapted_indepFun_increment (μ := μ) (B := B) hst hφ
  rw [hi.integral_fun_mul_eq_mul_integral ((hφ.mono (F.le s) le_rfl).aestronglyMeasurable)
    (D.increment_memLp s t hst).aestronglyMeasurable, D.centered_increment s t hst, mul_zero]

theorem memLp_adapted_mul_increment {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) (hφL2 : MemLp φ 2 μ) :
    MemLp (fun ω ↦ φ ω * (B t ω - B s ω)) 2 μ := by
  have hi := (adapted_indepFun_increment (μ := μ) (B := B) hst hφ).comp
    (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2) (by fun_prop) (by fun_prop)
  have hΔ := D.increment_memLp s t hst
  have hp : Integrable (fun ω ↦ φ ω ^ 2 * (B t ω - B s ω) ^ 2) μ :=
    hi.integrable_mul hφL2.integrable_sq hΔ.integrable_sq
  have hm : AEStronglyMeasurable (fun ω ↦ φ ω * (B t ω - B s ω)) μ :=
    ((hφ.mono (F.le s) le_rfl).aestronglyMeasurable).mul hΔ.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).mpr (by simpa only [mul_pow] using hp)

end IndependentL2Driver
end SHEStochastic
