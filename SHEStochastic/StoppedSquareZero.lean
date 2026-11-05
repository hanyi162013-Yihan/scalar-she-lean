module

public import SHEStochastic.ContinuousStoppedMartingaleTests
public import SHE.NullCompleteFiltration
public import BrownianMotion.Continuity.KolmogorovChentsov

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.StoppedSquareZero
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

theorem continuous_stopped (M : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (ω : Ω) (hc : Continuous (fun t ↦ M t ω)) :
    Continuous (fun t ↦ stoppedProcess M τ t ω) := by
  cases he : τ ω with
  | top =>
    simpa only [stoppedProcess, he, min_eq_left le_top, WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe] using hc
  | coe r =>
    simp only [stoppedProcess, he, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    convert hc.comp (continuous_id.min (continuous_const (y := r))) using 1 <;> rfl

/-- Continuity upgrades the fixed-time stopped equalities to one
common full-measure event, allowing later evaluation at arbitrary times. -/
theorem simultaneous_stopped_eq (M N : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t ↦ M t ω))
    (hcN : ∀ᵐ ω ∂μ, Continuous (fun t ↦ N t ω))
    (he : ∀ q, ∀ᵐ ω ∂μ, stoppedProcess M τ q ω = stoppedProcess N τ q ω) :
    ∀ᵐ ω ∂μ, ∀ q, stoppedProcess M τ q ω = stoppedProcess N τ q ω := by
  have hh := ProbabilityTheory.indistinguishable_of_edist_modification
    (hcM.mono fun ω hω ↦ continuous_stopped M τ ω hω)
    (hcN.mono fun ω hω ↦ continuous_stopped N τ ω hω)
    (fun q ↦ (he q).mono fun ω hω ↦ by rw [hω, edist_self])
  exact hh.mono fun ω hω q ↦ edist_eq_zero.mp (hω q)

/-- Remove one common null set before applying optional sampling.
Null completeness preserves adaptation; the result agrees at all times
simultaneously and hence also at random stopping times. -/
theorem continuous_version (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ M t ω)) :
    ∃ Z : ℝ≥0 → Ω → ℝ, Martingale Z F μ ∧
      (∀ ω, Continuous (fun t ↦ Z t ω)) ∧ (∀ᵐ ω ∂μ, ∀ t, Z t ω = M t ω) := by
  classical
  let Z (t : ℝ≥0) (ω : Ω) : ℝ := if Continuous (fun s ↦ M s ω) then M t ω else 0
  have he : ∀ᵐ ω ∂μ, ∀ t, Z t ω = M t ω :=
    hc.mono fun ω hω t ↦ if_pos hω
  have ha : StronglyAdapted F Z := fun t ↦
    SHE.NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t (hM.stronglyAdapted t)
      (he.mono fun ω hω ↦ hω t)
  refine ⟨Z, hM.congr ha (fun t ↦ he.mono fun ω hω ↦ (hω t).symm), ?_, he⟩
  intro ω
  by_cases hω : Continuous (fun s ↦ M s ω)
  · simpa only [Z, if_pos hω] using hω
  · simpa only [Z, if_neg hω] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ)))

/-- Optional stopping also applies to an almost surely continuous
martingale in a null-complete filtration. The existing continuous
version preserves the entire stopped trajectory on one common event. -/
theorem stopped_martingale (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ M t ω))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess M τ) F μ := by
  obtain ⟨Z, hZ, hcZ, he⟩ := continuous_version μ F hnull M hM hc
  have hs := hZ.stoppedProcess (fun ω _ ↦ (hcZ ω).continuousAt.continuousWithinAt) hτ
  have heq := stoppedProcess_congr (τ := τ) he
  exact hs.congr (fun t ↦ SHE.NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t
    (hs.stronglyAdapted t) (heq.mono fun ω hω ↦ (hω t).symm))
      (fun t ↦ heq.mono fun ω hω ↦ hω t)

/-- If the compensator vanishes at a stopped time, the corresponding
stochastic integral vanishes there. Only the square-compensator
martingale is needed, so the result applies to arbitrary L2 integrands. -/
theorem stopped_zero (hnull : SHE.NullCompleteFiltration.ContainsNullSets F μ)
    (M A : ℝ≥0 → Ω → ℝ)
    (hN : Martingale (fun t ω ↦ M t ω ^ 2 - A t ω) F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ M t ω ^ 2 - A t ω))
    (hzero : ∀ᵐ ω ∂μ, M 0 ω ^ 2 - A 0 ω = 0)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ) (q : ℝ≥0)
    (hA : ∀ᵐ ω ∂μ, stoppedProcess A τ q ω = 0) :
    ∀ᵐ ω ∂μ, stoppedProcess M τ q ω = 0 := by
  obtain ⟨Z, hZ, hZc, he⟩ := continuous_version μ F hnull _ hN hc
  have hZs := hZ.stoppedProcess (fun ω _ ↦ (hZc ω).continuousAt.continuousWithinAt) hτ
  have hinit : (fun ω ↦ stoppedProcess Z τ 0 ω) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    filter_upwards [he, hzero] with ω hω hz
    simpa [stoppedProcess] using (hω 0).trans hz
  have hmean : (∫ ω, stoppedProcess Z τ q ω ∂μ) = 0 := by
    have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hZs
      0 q bot_le (fun _ ↦ (1 : ℝ)) stronglyMeasurable_const 1 (fun _ ↦ by norm_num)
    have hi := hZs.integrable
    simpa only [one_mul, integral_sub (hi q) (hi 0), integral_congr_ae hinit,
      integral_zero, sub_zero] using hh
  have hs : (fun ω ↦ stoppedProcess Z τ q ω) =ᵐ[μ]
      fun ω ↦ stoppedProcess M τ q ω ^ 2 := by
    filter_upwards [he, hA] with ω hω hAω
    have hh := hω (min (q : WithTop ℝ≥0) (τ ω)).untopA
    change stoppedProcess Z τ q ω = stoppedProcess M τ q ω ^ 2 - stoppedProcess A τ q ω at hh
    simpa only [hAω, sub_zero] using hh
  have hi : Integrable (fun ω ↦ stoppedProcess M τ q ω ^ 2) μ := (hZs.integrable q).congr hs
  have hh : (∫ ω, stoppedProcess M τ q ω ^ 2 ∂μ) = 0 := by
    rw [← integral_congr_ae hs]
    exact hmean
  exact ((integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg _) hi).mp hh).mono
    fun ω hω ↦ (sq_eq_zero_iff).mp hω

end SHEStochastic.StoppedSquareZero
