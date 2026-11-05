module

public import SHEStochastic.ParameterPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.JointContinuousVersion
open MeasureTheory Set Filter
open scoped NNReal Topology

/-- Jointly past-measurable fixed-time representatives and continuous
individual versions produce a jointly predictable version. A countable
left grid gives simultaneous equality at every time on one sample event. -/
theorem exists_joint {X Ω : Type*} [mX : MeasurableSpace X] [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω)
    (V : ℝ≥0 → X × Ω → ℝ)
    (hV : ∀ t, @Measurable (X × Ω) ℝ (mX.prod (F t)) _ (V t))
    (U : X → ℝ≥0 → Ω → ℝ)
    (hU : ∀ x ω, Continuous (fun t ↦ U x t ω))
    (hrep : ∀ x t, (fun ω ↦ V t (x, ω)) =ᵐ[μ] U x t) :
    ∃ Y : X × (ℝ≥0 × Ω) → ℝ, StronglyMeasurable[mX.prod F.predictable] Y ∧
      (∀ x, ∀ᵐ ω ∂μ, ∀ t, Y (x, (t, ω)) = U x t ω) := by
  let P := ParameterPredictable.filtration (X := X) F
  have hVa : StronglyAdapted P V := fun t ↦ (hV t).stronglyMeasurable
  let A (n : ℕ) (z : X × (ℝ≥0 × Ω)) :=
    SHE.ContinuousPredictable.approximation V n (z.2.1, (z.1, z.2.2))
  have hA (n : ℕ) : StronglyMeasurable[mX.prod F.predictable] (A n) :=
    (SHE.ContinuousPredictable.approximation_predictable P V hVa n).comp_measurable
      (ParameterPredictable.transpose F)
  let Y (z : X × (ℝ≥0 × Ω)) := limUnder atTop (fun n ↦ A n z)
  have hY : StronglyMeasurable[mX.prod F.predictable] Y := by
    letI : MeasurableSpace (X × (ℝ≥0 × Ω)) := mX.prod F.predictable
    exact StronglyMeasurable.limUnder hA
  refine ⟨Y, hY, ?_⟩
  intro x
  have hgrid : ∀ᵐ ω ∂μ, ∀ n k : ℕ,
      V (SHE.ApproximationCells.point n k) (x, ω) =
        U x (SHE.ApproximationCells.point n k) ω :=
    ae_all_iff.mpr (fun n ↦ ae_all_iff.mpr (fun k ↦ hrep x (SHE.ApproximationCells.point n k)))
  filter_upwards [hgrid] with ω hω
  intro t
  have hAt (n : ℕ) : A n (x, (t, ω)) = U x (SHE.ContinuousPredictable.leftPoint n t) ω :=
    hω n (SHE.ApproximationCells.index n t - 1)
  have hlim : Tendsto (fun n ↦ A n (x, (t, ω))) atTop (𝓝 (U x t ω)) := by
    rw [show (fun n ↦ A n (x, (t, ω))) =
      (fun n ↦ U x (SHE.ContinuousPredictable.leftPoint n t) ω) from funext hAt]
    exact (hU x ω).continuousAt.tendsto.comp (SHE.ContinuousPredictable.leftPoint_tendsto t)
  exact hlim.limUnder_eq

end SHEStochastic.JointContinuousVersion
