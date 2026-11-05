module

public import SHEStochastic.NativeCellPullout
public import SHE.LpDominatedLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.PredictableMultiplier
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- A bounded predictable scalar multiplier acts on the original L²
input. This is the existing contraction construction with a general bound. -/
theorem memLp (u : Process (E := C) F μ H) (a : ℝ≥0 × Ω → ℝ)
    (ha : StronglyMeasurable[F.predictable] a) (B : ℝ) (hb : ∀ p, |a p| ≤ B) :
    @MemLp _ _ F.predictable _ _ (fun p ↦ a p • u p) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  apply (Lp.memLp u).of_le_mul (c := B) (ha.smul (Lp.stronglyMeasurable u)).aestronglyMeasurable
  filter_upwards with p
  change ‖a p • u p‖ ≤ B * ‖u p‖
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)

def process (u : Process (E := C) F μ H) (a : ℝ≥0 × Ω → ℝ)
    (ha : StronglyMeasurable[F.predictable] a) (B : ℝ) (hb : ∀ p, |a p| ≤ B) :
    Process (E := C) F μ H :=
  (memLp u a ha B hb).toLp (fun p ↦ a p • u p)

theorem process_ae_trim (u : Process (E := C) F μ H) (a : ℝ≥0 × Ω → ℝ)
    (ha : StronglyMeasurable[F.predictable] a) (B : ℝ) (hb : ∀ p, |a p| ≤ B) :
    process u a ha B hb =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
      (fun p ↦ a p • u p) := (memLp u a ha B hb).coeFn_toLp

theorem process_ae (u : Process (E := C) F μ H) (a : ℝ≥0 × Ω → ℝ)
    (ha : StronglyMeasurable[F.predictable] a) (B : ℝ) (hb : ∀ p, |a p| ≤ B) :
    process u a ha B hb =ᵐ[energyMeasure μ H] (fun p ↦ a p • u p) :=
  ae_eq_of_ae_eq_trim (process_ae_trim u a ha B hb)

theorem norm_process_le (u : Process (E := C) F μ H) (a : ℝ≥0 × Ω → ℝ)
    (ha : StronglyMeasurable[F.predictable] a) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ p, |a p| ≤ B) :
    ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      ‖process u a ha B hb p‖ ≤ ‖(B • u) p‖ := by
  filter_upwards [process_ae_trim u a ha B hb, Lp.coeFn_smul B u] with p hp hs
  rw [hp, hs]
  change ‖a p • u p‖ ≤ ‖B • u p‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hB]
  exact mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)

/-- A deterministic time cell, with a bounded coefficient known at its
left endpoint, integrates to that coefficient times the actual increment. -/
theorem cell (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H)
    (s t : ℝ≥0) (hst : s ≤ t) (Z : Ω → ℝ) (hZ : StronglyMeasurable[F s] Z)
    (B : ℝ) (hB : 0 ≤ B) (hZb : ∀ ω, |Z ω| ≤ B) :
    ∃ v : Process (E := C) F μ H,
      v =ᵐ[energyMeasure μ H] (fun p ↦ PredictableSteps.step s t Z p • u p) ∧
      J.integral v =ᵐ[μ] (fun ω ↦ Z ω *
        (J.integral (StoppedItoInputs.stop F μ H t u) ω -
          J.integral (StoppedItoInputs.stop F μ H s u) ω)) := by
  obtain ⟨v, hv, hJ⟩ := BoundedPastItoMultiplier.increment F μ H s J hlocal t hst u Z hZ B hB hZb
  refine ⟨v, ?_, hJ⟩
  have he : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 ≠ t :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne t)
  filter_upwards [hv, he] with p hp hne
  rw [hp]
  by_cases hps : s < p.1 <;> by_cases hpt : p.1 < t
  · simp [PredictableSteps.step, Set.mem_Ioc, hps, hpt, hpt.le]
  · have hn : ¬p.1 ≤ t := not_le.mpr (lt_of_le_of_ne (le_of_not_gt hpt) hne.symm)
    simp [PredictableSteps.step, Set.mem_Ioc, hps, hpt, hn]
  · simp [PredictableSteps.step, Set.mem_Ioc, hps, hpt]
  · simp [PredictableSteps.step, Set.mem_Ioc, hps, hpt]

end SHEStochastic.PredictableMultiplier
