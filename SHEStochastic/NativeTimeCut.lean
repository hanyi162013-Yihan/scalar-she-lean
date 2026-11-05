module

public import SHEStochastic.NativeEnergy
public import SHEStochastic.FiniteCylindricalTerminalIto
public import SHEStochastic.PredictableBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeTimeCut
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H

def after (s : ℝ≥0) (u : Lp C 2 νin) : Lp C 2 νin :=
  ((Lp.memLp u).indicator (measurableSet_predictable_Ioi_prod
    (𝓕 := F) (i := s) MeasurableSet.univ).nullMeasurableSet).toLp
      ((Set.Ioi s ×ˢ Set.univ).indicator u)

def prior (s : ℝ≥0) (u : Lp C 2 νin) : Lp C 2 νin := u - after s u

theorem after_ae (s : ℝ≥0) (u : Lp C 2 νin) :
    after s u =ᵐ[νin] (fun p ↦ if s < p.1 then u p else 0) := by
  have h := ((Lp.memLp u).indicator (measurableSet_predictable_Ioi_prod
    (𝓕 := F) (i := s) MeasurableSet.univ).nullMeasurableSet).coeFn_toLp
  exact h.mono fun p hp ↦ by
    simpa only [after, Set.indicator, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true] using hp

theorem prior_ae (s : ℝ≥0) (u : Lp C 2 νin) :
    prior s u =ᵐ[νin] (fun p ↦ if s < p.1 then 0 else u p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [Lp.coeFn_sub u (after s u), after_ae s u] with p hp ha
  change (u - after s u) p = _
  rw [hp, Pi.sub_apply, ha]
  split_ifs <;> simp

theorem after_supported (s : ℝ≥0) (u : Lp C 2 νin) :
    ∀ᵐ p ∂νin, p.1 ≤ s → after s u p = 0 := by
  filter_upwards [after_ae s u] with p hp hs
  change after s u p = _
  rw [hp, if_neg (not_lt.mpr hs)]

theorem prior_supported (s : ℝ≥0) (u : Lp C 2 νin) :
    ∀ᵐ p ∂νin, s < p.1 → prior s u p = 0 := by
  filter_upwards [prior_ae s u] with p hp hs
  change prior s u p = _
  rw [hp, if_pos hs]

theorem split (s : ℝ≥0) (u : Lp C 2 νin) : prior s u + after s u = u := sub_add_cancel _ _

/-- The two time pieces have disjoint energies, including without any
chosen regularity of the input's paths. -/
theorem energy_split (s : ℝ≥0) (u : Lp C 2 νin) :
    NativeEnergy.energy u =ᵐ[μ]
      (fun ω ↦ NativeEnergy.energy (prior s u) ω + NativeEnergy.energy (after s u) ω) := by
  have hp := NativeEnergy.energy_ae_of_ae _ _ (prior_ae s u)
  have ha := NativeEnergy.energy_ae_of_ae _ _ (after_ae s u)
  have hu := (NativeEnergy.product_memLp u).norm.integrable_sq
  filter_upwards [hp, ha, hu.prod_left_ae] with ω hp ha huω
  change NativeEnergy.energy u ω = _
  rw [hp, ha]
  have hle : Integrable (fun r ↦ (Set.Iic s).indicator (fun r ↦ ‖u (r, ω)‖ ^ 2) r) νt :=
    huω.indicator measurableSet_Iic
  have hgt : Integrable (fun r ↦ (Set.Ioi s).indicator (fun r ↦ ‖u (r, ω)‖ ^ 2) r) νt :=
    huω.indicator measurableSet_Ioi
  have he1 : (fun r ↦ ‖if s < r then (0 : C) else u (r, ω)‖ ^ 2) =
      (Set.Iic s).indicator (fun r ↦ ‖u (r, ω)‖ ^ 2) := by
    funext r
    by_cases hr : s < r <;> simp [hr, Set.indicator, not_lt]
  have he2 : (fun r ↦ ‖if s < r then u (r, ω) else (0 : C)‖ ^ 2) =
      (Set.Ioi s).indicator (fun r ↦ ‖u (r, ω)‖ ^ 2) := by
    funext r
    by_cases hr : s < r <;> simp [hr, Set.indicator]
  change (∫ r, ‖u (r, ω)‖ ^ 2 ∂νt) =
    (∫ r, ‖if s < r then (0 : C) else u (r, ω)‖ ^ 2 ∂νt) +
      ∫ r, ‖if s < r then u (r, ω) else (0 : C)‖ ^ 2 ∂νt
  rw [he1, he2, ← integral_add hle hgt]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r ↦ by
    by_cases hr : s < r <;> simp [Set.indicator, hr, not_lt]

theorem energy_prior_le (s : ℝ≥0) (u : Lp C 2 νin) :
    NativeEnergy.energy (prior s u) ≤ᵐ[μ] NativeEnergy.energy u := by
  filter_upwards [energy_split s u] with ω hω
  change NativeEnergy.energy (prior s u) ω ≤ _
  rw [hω]
  exact le_add_of_nonneg_right (integral_nonneg fun _ ↦ sq_nonneg _)

theorem energy_after_le (s : ℝ≥0) (u : Lp C 2 νin) :
    NativeEnergy.energy (after s u) ≤ᵐ[μ] NativeEnergy.energy u := by
  filter_upwards [energy_split s u] with ω hω
  change NativeEnergy.energy (after s u) ω ≤ _
  rw [hω]
  exact le_add_of_nonneg_left (integral_nonneg fun _ ↦ sq_nonneg _)

def priorEnergy (s : ℝ≥0) (u : Lp C 2 νin) (ω : Ω) : ℝ :=
  ∫ r, (Set.Iic s).indicator (fun r ↦ ‖u (r, ω)‖ ^ 2) r ∂νt

theorem priorEnergy_adapted (s : ℝ≥0) (u : Lp C 2 νin) :
    StronglyMeasurable[F s] (priorEnergy s u) := by
  letI : NullSingletonClass MathFin.ItoIntegralL2.timeMeasure :=
    ⟨MathFin.ItoIntegralL2.timeMeasure_singleton⟩
  haveI : NullSingletonClass νt := by dsimp [MathFin.ItoIntegralCLM.timeMeasure_T]; infer_instance
  have hh := PredictableBracket.stronglyMeasurable_primitive (F := F) νt
    (fun p ↦ ‖u p‖ ^ 2) ((Lp.stronglyMeasurable u).norm.pow 2) s
  convert hh using 1
  funext ω
  apply integral_congr_ae
  filter_upwards [(νt).ae_ne s] with r hr
  by_cases hrs : r < s <;> simp_all [priorEnergy, Set.indicator, le_iff_lt_or_eq]

theorem energy_prior_ae (s : ℝ≥0) (u : Lp C 2 νin) :
    NativeEnergy.energy (prior s u) =ᵐ[μ] priorEnergy s u := by
  have hh := NativeEnergy.energy_ae_of_ae _ _ (prior_ae s u)
  filter_upwards [hh] with ω hω
  change NativeEnergy.energy (prior s u) ω = _
  rw [hω]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r ↦ by
    by_cases hr : s < r <;> simp [priorEnergy, Set.indicator, hr, not_lt]

end SHEStochastic.NativeTimeCut
