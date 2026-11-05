module

public import SHEStochastic.FiniteScalarItoStopping

/-! The complete scalar terminal interface from the paper's finite-horizon
coordinate law, on its original filtered probability space. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FiniteScalarItoProcess
open MeasureTheory ProbabilityTheory FiniteScalarIto
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : Coordinates F μ H ι)
local notation "ν" => inputMeasure F μ H

theorem rawIsometry_eq_prefix_of_vanishes_after (i : ι) (t : ℝ≥0) (ht : t ≤ H)
    (v : Lp ℝ 2 ν) (hv : ∀ᵐ p ∂ν, t < p.1 → v p = 0) :
    rawIsometry P i v = prefixCLM P i t v := by
  letI : Fact (F t ≤ ‹MeasurableSpace Ω›) := ⟨F.le t⟩
  have hband : (∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), v z ^ 2 ∂ν) =
      ∫ z, v z ^ 2 ∂ν := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hv, FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F)
      (μ := μ) H (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with z hz hzH hnot
    rw [hz (by by_contra hc; exact hnot ⟨⟨hzH.1, not_lt.mp hc⟩, Set.mem_univ _⟩)]
    ring
  have hn : ‖(condExpL2 ℝ ℝ (F.le t) (rawIsometry P i v) : Lp ℝ 2 μ)‖ =
      ‖rawIsometry P i v‖ := by
    rw [← prefixCLM_eq_condExpL2]
    have hs : ‖prefixCLM P i t v‖ ^ 2 = ‖rawIsometry P i v‖ ^ 2 := by
      rw [prefixCLM_norm_sq P i t ht, hband, (rawIsometry P i).norm_map,
        MathFin.ItoIntegralL2.lp_two_norm_sq v]
    have h := congrArg Real.sqrt hs
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  rw [prefixCLM_eq_condExpL2]
  change rawIsometry P i v = (lpMeas ℝ ℝ (F t) 2 μ).starProjection (rawIsometry P i v)
  exact (Submodule.starProjection_eq_self_iff.mpr
    ((Submodule.mem_iff_norm_starProjection _ _).mpr hn)).symm

/-- A complete scalar terminal integral using only the recognized coordinate
laws through H. No Brownian extension or change of probability space is used. -/
def terminalIto (i : ι) : SHE.StandardTerminalIto (C := ℝ) (E := ℝ) F μ H where
  integral := FiniteScalarIto.integral P i
  centered := integral_centered P i
  adapted t v hv := by
    let f := FilteredScalarIto.processTransport (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) v
    have ha : AEStronglyMeasurable[F t] (FiniteScalarIto.integral P i v : Ω → ℝ) μ := by
      change AEStronglyMeasurable[F t] (rawIsometry P i f : Ω → ℝ) μ
      by_cases ht : t ≤ H
      · rw [rawIsometry_eq_prefix_of_vanishes_after P i t ht f
          (FilteredScalarIto.processTransport_stopped (𝓖 := F) H t
            (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) v hv)]
        exact prefixCLM_adapted P i t f
      · have h := prefixCLM_adapted P i H f
        rw [prefixCLM_terminal] at h
        exact h.mono (F.mono (le_of_not_ge ht))
    exact ⟨ha.mk _, ha.stronglyMeasurable_mk, ha.ae_eq_mk⟩

end SHEStochastic.FiniteScalarItoProcess
