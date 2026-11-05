module

public import SHEStochastic.PredictableMultiplier
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.UnboundedPastMultiplier
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- A coefficient known at the left endpoint may be unbounded: only
the weighted cell itself must be in the original predictable L² space.
The bounded cell rule and dominated convergence prove the pullout. -/
theorem cell (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u v : Process (E := C) F μ H)
    (s t : ℝ≥0) (hst : s ≤ t) (Z : Ω → ℝ) (hZ : StronglyMeasurable[F s] Z)
    (hv : v =ᵐ[energyMeasure μ H] (fun p ↦ PredictableSteps.step s t Z p • u p)) :
    J.integral v =ᵐ[μ] (fun ω ↦ Z ω *
      (J.integral (StoppedItoInputs.stop F μ H t u) ω -
        J.integral (StoppedItoInputs.stop F μ H s u) ω)) := by
  let Zn (n : ℕ) (ω : Ω) : ℝ := if |Z ω| ≤ (n : ℝ) then Z ω else 0
  have hZn (n : ℕ) : StronglyMeasurable[F s] (Zn n) :=
    hZ.ite (measurableSet_le hZ.norm.measurable measurable_const) stronglyMeasurable_const
  have hZb (n : ℕ) (ω : Ω) : |Zn n ω| ≤ (n : ℝ) := by
    dsimp only [Zn]
    split_ifs with hn
    · exact hn
    · simp
  have hc (n : ℕ) := PredictableMultiplier.cell J hlocal u s t hst (Zn n) (hZn n)
    n (Nat.cast_nonneg n) (hZb n)
  choose V hV hJ using hc
  have hclip (n : ℕ) : V n =ᵐ[energyMeasure μ H]
      (fun p ↦ if |Z p.2| ≤ (n : ℝ) then v p else 0) := by
    filter_upwards [hV n, hv] with p hp hq
    change V n p = _ at hp
    change v p = _ at hq
    rw [hp]
    by_cases hn : |Z p.2| ≤ (n : ℝ)
    · rw [if_pos hn, hq]
      simp only [PredictableSteps.step, Set.indicator_apply, Zn, hn, ite_true]
    · rw [if_neg hn]
      simp only [PredictableSteps.step, Set.indicator_apply, Zn, hn, ite_false]
      split_ifs <;> simp
  have hdom (n : ℕ) : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      ‖V n p‖ ≤ ‖v p‖ := by
    have hd : ∀ᵐ p ∂energyMeasure μ H, ‖V n p‖ ≤ ‖v p‖ := by
      filter_upwards [hclip n] with p hp
      change V n p = if |Z p.2| ≤ (n : ℝ) then v p else 0 at hp
      rw [hp]
      split_ifs <;> simp
    rw [ae_iff] at hd ⊢
    exact (trim_measurableSet_eq (predictable_le_product F)
      (measurableSet_le (Lp.stronglyMeasurable (V n)).norm.measurable
        (Lp.stronglyMeasurable v).norm.measurable).compl).trans hd
  have hlim : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F),
      Tendsto (fun n ↦ V n p) atTop (𝓝 (v p)) := by
    have ha : ∀ᵐ p ∂energyMeasure μ H, Tendsto (fun n ↦ V n p) atTop (𝓝 (v p)) := by
      filter_upwards [ae_all_iff.mpr hclip] with p hp
      apply Tendsto.congr' _ tendsto_const_nhds
      have hn : ∀ᶠ n : ℕ in atTop, |Z p.2| ≤ (n : ℝ) :=
        eventually_atTop.2 ⟨⌈|Z p.2|⌉₊, fun n hn ↦
          (Nat.le_ceil _).trans (by exact_mod_cast hn)⟩
      filter_upwards [hn] with n hn
      exact ((hp n).trans (if_pos hn)).symm
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    rw [ae_iff] at ha ⊢
    exact (trim_measurableSet_eq (predictable_le_product F)
      (measurableSet_tendsto_fun (fun n ↦ (Lp.stronglyMeasurable (V n)).measurable)
        (Lp.stronglyMeasurable v).measurable).compl).trans ha
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hLp := LpDominatedLimit.tendsto v v V hdom
    (Eventually.of_forall fun _ ↦ le_rfl) hlim
  have hi := tendstoInMeasure_of_tendsto_Lp (J.integral.continuous.tendsto v |>.comp hLp)
  have hr : TendstoInMeasure μ
      (fun n ω ↦ Zn n ω * (J.integral (StoppedItoInputs.stop F μ H t u) ω -
        J.integral (StoppedItoInputs.stop F μ H s u) ω)) atTop
      (fun ω ↦ Z ω * (J.integral (StoppedItoInputs.stop F μ H t u) ω -
        J.integral (StoppedItoInputs.stop F μ H s u) ω)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hZn n).mono (F.le s)).aestronglyMeasurable.mul
        ((Lp.stronglyMeasurable _).sub (Lp.stronglyMeasurable _)).aestronglyMeasurable
    · filter_upwards with ω
      apply Tendsto.congr' _ tendsto_const_nhds
      have hn : ∀ᶠ n : ℕ in atTop, |Z ω| ≤ (n : ℝ) :=
        eventually_atTop.2 ⟨⌈|Z ω|⌉₊, fun n hn ↦
          (Nat.le_ceil _).trans (by exact_mod_cast hn)⟩
      filter_upwards [hn] with n hn
      simp only [Zn, if_pos hn]
  exact tendstoInMeasure_ae_unique hi (TendstoInMeasure.congr_left (fun n ↦ (hJ n).symm) hr)

end SHEStochastic.UnboundedPastMultiplier
