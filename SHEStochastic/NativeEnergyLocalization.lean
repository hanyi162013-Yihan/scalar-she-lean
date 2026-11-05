module

public import SHEStochastic.NativePredictableEnergy
public import SHEStochastic.TimeEnergyCap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeEnergyLocalization
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

/-- Localize a native predictable L2 input at its running energy.
The approximants converge in the native L2 norm and their energies are
bounded both by the original energy and by the deterministic level. -/
theorem exists_sequence {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ C) (u : Lp C 2 νin) :
    ∃ U : ℕ → Lp C 2 νin,
      (∀ n, ∀ᵐ ω ∂μ, NativeEnergy.energy (U n) ω ≤ min (NativeEnergy.energy u ω) (n : ℝ)) ∧
      Filter.Tendsto U Filter.atTop (𝓝 u) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨A, hA, hAeq⟩ := NativePredictableEnergy.exists_version e u
  let S (n : ℕ) : Set (ℝ≥0 × Ω) := {p | A p.1 p.2 < (n : ℝ)}
  have hS (n : ℕ) : MeasurableSet[F.predictable] (S n) :=
    measurableSet_lt hA.measurable measurable_const
  let hm (n : ℕ) := (Lp.memLp u).indicator (hS n).nullMeasurableSet
  let U (n : ℕ) : Lp C 2 νin := (hm n).toLp ((S n).indicator u)
  have hU (n : ℕ) : U n =ᵐ[νin] (S n).indicator u := (hm n).coeFn_toLp
  refine ⟨U, ?_, ?_⟩
  · intro n
    have hE := NativeEnergy.energy_ae_of_ae (U n) _ (hU n)
    filter_upwards [hE, hAeq, (NativeEnergy.product_memLp u).norm.integrable_sq.prod_left_ae]
      with ω hEω hAω hiω
    rw [hEω]
    have he : (fun r ↦ ‖(S n).indicator u (r, ω)‖ ^ 2) =
        {r | TimeEnergyCap.primitive (H := H) (fun r ↦ ‖u (r, ω)‖ ^ 2) r < (n : ℝ)}.indicator
          (fun r ↦ ‖u (r, ω)‖ ^ 2) := by
      funext r
      have hAr : A r ω = TimeEnergyCap.primitive (H := H) (fun r ↦ ‖u (r, ω)‖ ^ 2) r := hAω r
      by_cases hr : A r ω < (n : ℝ) <;> simp [S, Set.indicator, ← hAr, hr]
    rw [he]
    exact TimeEnergyCap.capped_integral_le hiω (fun _ ↦ sq_nonneg _) (n : ℝ) (Nat.cast_nonneg _)
  · have hbound (n : ℕ) : ∀ᵐ p ∂νin, ‖(U n - u) p‖ ^ 2 ≤ ‖u p‖ ^ 2 := by
      filter_upwards [hU n, Lp.coeFn_sub (U n) u] with p hUp hs
      rw [hs, Pi.sub_apply, hUp]
      by_cases hp : p ∈ S n <;> simp [Set.indicator, hp]
    have hconv : ∀ᵐ p ∂νin, Filter.Tendsto (fun n : ℕ ↦ ‖(U n - u) p‖ ^ 2)
        Filter.atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [ae_all_iff.mpr hU, ae_all_iff.mpr (fun n ↦ Lp.coeFn_sub (U n) u)]
        with p hUp hs
      have hn : ∀ᶠ n : ℕ in Filter.atTop, A p.1 p.2 < (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (Filter.eventually_gt_atTop _)
      apply tendsto_const_nhds.congr'
      filter_upwards [hn] with n hn
      rw [hs n, Pi.sub_apply, hUp n, Set.indicator_of_mem (show p ∈ S n from hn)]
      simp
    have hsq : Filter.Tendsto (fun n : ℕ ↦ ‖U n - u‖ ^ 2) Filter.atTop (𝓝 0) := by
      have ht := tendsto_integral_filter_of_dominated_convergence (fun p ↦ ‖u p‖ ^ 2)
        (Filter.Eventually.of_forall fun n ↦ ((Lp.stronglyMeasurable (U n - u)).norm.pow 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun n ↦ (hbound n).mono fun p hp ↦ by
          simpa only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)] using hp)
        (Lp.memLp u).norm.integrable_sq hconv
      simpa only [Pi.pow_apply, L2EnergyContinuity.norm_sq, integral_zero] using ht
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

end SHEStochastic.NativeEnergyLocalization
