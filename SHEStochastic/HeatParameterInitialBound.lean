module

public import SHEStochastic.HeatParameterCoordinates
public import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.HeatParameterInitialBound
open MeasureTheory HeatParameterCover HeatParameterCoordinates

/-- Pointwise modification equalities become one simultaneous initial
zero event by separability and continuity, using the public theorem. -/
theorem simultaneous_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Parameter → Ω → ℝ) (hY : ∀ ω, Continuous (fun p ↦ Y p ω))
    (hz : ∀ p, Y (zeroTime p) =ᵐ[μ] 0) :
    ∀ᵐ ω ∂μ, ∀ p, Y (zeroTime p) ω = 0 := by
  have hh := ProbabilityTheory.indistinguishable_of_edist_modification
    (Filter.Eventually.of_forall (fun ω ↦ (hY ω).comp continuous_zeroTime))
    (Filter.Eventually.of_forall (fun _ : Ω ↦ (continuous_const : Continuous (fun _ : Parameter ↦ (0 : ℝ)))))
    (fun p ↦ (hz p).mono fun ω h ↦ by
      change edist (Y (zeroTime p) ω) 0 = 0
      simpa only [Pi.zero_apply, h] using edist_self (0 : ℝ))
  exact hh.mono fun _ h p ↦ edist_eq_zero.mp (h p)

theorem bounded (f : Parameter → ℝ) (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p, |f p| ≤ M := by
  let g : C(Parameter, ℝ) := ⟨f, hf⟩
  exact ⟨‖g‖, norm_nonneg _, fun p ↦ g.norm_coe_le_norm p⟩

/-- A continuous modification with zero initial line vanishes uniformly
in its spatial parameter. No continuity of the initial heat evolution
in the uniform norm is needed. -/
theorem uniformly_small (f : Parameter → ℝ) (hf : Continuous f)
    (hz : ∀ p, f (zeroTime p) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : Parameter, |p.val 0| < δ → |f p| < ε := by
  obtain ⟨δ, hδ, hh⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  refine ⟨δ, hδ, fun p hp ↦ ?_⟩
  have hb := hh (show dist p (zeroTime p) < δ from (zeroTime_distance p).trans_lt hp)
  simpa only [hz p, Real.dist_eq, sub_zero] using hb

end SHEStochastic.HeatParameterInitialBound
