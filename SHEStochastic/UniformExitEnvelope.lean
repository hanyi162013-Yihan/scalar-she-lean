module

public import SHEStochastic.PhysicalHeatParameterSection
public import SHEStochastic.UnboundedMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UniformExitEnvelope
open MeasureTheory SHE SHE.StoppedFourier AddCircle HeatParameterCover HeatParameterPullback
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem bound (heat : ShortTime → Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)))
    (M : ℝ) (hM : 0 ≤ M)
    (hheat : ∀ t, L2ExtendedUniformNorm.value haarAddCircle (heat t) ≤ ENNReal.ofReal M)
    (Y : C(Parameter, ℝ)) (t : ShortTime) :
    L2ExtendedUniformNorm.value haarAddCircle (heat t + PhysicalHeatParameterSection.value 2 Y t) ≤
      ENNReal.ofReal (M + ‖PhysicalHeatParameterSection.path ∞ Y‖) := by
  calc
    _ ≤ L2ExtendedUniformNorm.value haarAddCircle (heat t) +
        L2ExtendedUniformNorm.value haarAddCircle (PhysicalHeatParameterSection.value 2 Y t) :=
      L2ExtendedUniformNorm.add_le _ _ _
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal ‖PhysicalHeatParameterSection.value ∞ Y t‖ := by
      rw [PhysicalHeatParameterSection.uniform_norm_eq]
      exact add_le_add (hheat t) le_rfl
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal ‖PhysicalHeatParameterSection.path ∞ Y‖ :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal ((PhysicalHeatParameterSection.path ∞ Y).norm_coe_le_norm t))
    _ = _ := (ENNReal.ofReal_add hM (norm_nonneg _)).symm

/-- The scalar uniform norm is continuous initially, even when the
bounded initial function itself has no uniform-norm continuous heat
orbit. L2 continuity, heat contraction and the vanishing remainder are
sufficient, via lower semicontinuity of the extended L2 state norm. -/
theorem initial_norm_continuity
    (heat : ShortTime → Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)))
    (hheatc : ContinuousAt heat initialTime) (M : ℝ) (hM : 0 ≤ M)
    (hheat : ∀ t, L2ExtendedUniformNorm.value haarAddCircle (heat t) ≤ ENNReal.ofReal M)
    (hinitial : L2ExtendedUniformNorm.value haarAddCircle (heat initialTime) = ENNReal.ofReal M)
    (Y : C(Parameter, ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p) = 0) :
    ContinuousAt (fun t ↦ L2ExtendedUniformNorm.value haarAddCircle
      (heat t + PhysicalHeatParameterSection.value 2 Y t)) initialTime := by
  let B (t : ShortTime) := ENNReal.ofReal (M + ‖PhysicalHeatParameterSection.value ∞ Y t‖)
  have hb (t : ShortTime) : L2ExtendedUniformNorm.value haarAddCircle
      (heat t + PhysicalHeatParameterSection.value 2 Y t) ≤ B t := by
    calc
      _ ≤ L2ExtendedUniformNorm.value haarAddCircle (heat t) +
          L2ExtendedUniformNorm.value haarAddCircle (PhysicalHeatParameterSection.value 2 Y t) :=
        L2ExtendedUniformNorm.add_le _ _ _
      _ ≤ ENNReal.ofReal M + ENNReal.ofReal ‖PhysicalHeatParameterSection.value ∞ Y t‖ := by
        rw [PhysicalHeatParameterSection.uniform_norm_eq]
        exact add_le_add (hheat t) le_rfl
      _ = B t := (ENNReal.ofReal_add hM (norm_nonneg _)).symm
  apply L2ExtendedUniformNorm.continuousAt_of_envelope haarAddCircle
    (fun t ↦ heat t + PhysicalHeatParameterSection.value 2 Y t) initialTime
    (hheatc.add (PhysicalHeatParameterSection.uniformContinuous_value 2 Y).continuous.continuousAt)
    B (ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.add (PhysicalHeatParameterSection.uniformContinuous_value ∞ Y).continuous.continuousAt.norm))
    (Filter.Eventually.of_forall hb)
  simp only [B, PhysicalHeatParameterSection.value_initial _ Y hz, add_zero, norm_zero, hinitial]

/-- Finite compact physical remainder norms give vanishing uniform
exit probabilities. No a priori global stochastic moment bound is
introduced; measurability follows from the actual random path. -/
theorem tails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (heat : ShortTime → Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)))
    (M : ℝ) (hM : 0 ≤ M)
    (hheat : ∀ t, L2ExtendedUniformNorm.value haarAddCircle (heat t) ≤ ENNReal.ofReal M)
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ ω, Continuous (fun p ↦ Y p ω)) :
    Filter.Tendsto (fun n : ℕ ↦ μ {ω | ∃ t : ShortTime, (n : ℝ≥0∞) ≤
      L2ExtendedUniformNorm.value haarAddCircle
        (heat t + PhysicalHeatParameterSection.value 2 ⟨fun p ↦ Y p ω, hc ω⟩ t)})
      Filter.atTop (nhds 0) := by
  let Q (ω : Ω) : C(Parameter, ℝ) := ⟨fun p ↦ Y p ω, hc ω⟩
  let D (ω : Ω) := M + ‖PhysicalHeatParameterSection.path ∞ (Q ω)‖
  have hD : Measurable D := measurable_const.add
    (PhysicalHeatParameterSection.stronglyMeasurable_random_path ∞ Y hm hc).norm.measurable
  apply UnboundedMomentBounds.exit_vanishes μ D hD
  intro n ω hω
  obtain ⟨t, ht⟩ := hω
  have hh := ht.trans (bound heat M hM hheat (Q ω) t)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  change (n : ℝ) ≤ M + ‖PhysicalHeatParameterSection.path ∞ (Q ω)‖
  simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (add_nonneg hM (norm_nonneg _))] using hr

end SHEStochastic.UniformExitEnvelope
