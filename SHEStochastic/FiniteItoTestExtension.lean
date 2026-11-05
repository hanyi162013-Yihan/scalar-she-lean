module

public import SHEStochastic.ClampedAbsoluteContinuity
public import SHE.GaussianItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.FiniteItoTestExtension
open MeasureTheory Set SHE.GaussianItoTest ClampedAbsoluteContinuity
open scoped NNReal Topology

variable {n : ℕ} {a b : ℝ} {G dG : ℝ → State n → ℝ}

def value (a b : ℝ) (G : ℝ → State n → ℝ) (r : ℝ) : State n → ℝ := G (clamp a b r)

def derivative (a b : ℝ) (dG : ℝ → State n → ℝ) (r : ℝ) (z : State n) : ℝ :=
  (Ioo a b).indicator (fun r ↦ dG r z) r

/-- The existing regular test extends constantly in time outside its
original interval. Absolute continuity is preserved without any new
smoothness assumption on the time derivative. -/
theorem regular (hab : a ≤ b) (hG : RegularTest a b G dG) (H : ℝ≥0) :
    RegularTest 0 (H : ℝ) (value a b G) (derivative a b dG) := by
  have hk : Continuous (fun p : ℝ × State n ↦ (clamp a b p.1, p.2)) :=
    ((lipschitz a b).continuous.comp continuous_fst).prodMk continuous_snd
  refine
    { continuous := hG.continuous.comp hk
      state_smooth := fun r ↦ hG.state_smooth _
      gradient_continuous := hG.gradient_continuous.comp hk
      hessian_continuous := hG.hessian_continuous.comp hk
      time_absolutelyContinuous := fun z ↦ extension hab (hG.time_absolutelyContinuous z) 0 H
      time_derivative := ?_
      derivative_measurable := ?_
      derivative_state_continuous := ?_
      derivative_envelope := ?_
      bounds := ?_ }
  · filter_upwards [hG.time_derivative, volume.ae_ne a, volume.ae_ne b] with r hd hra hrb
    intro hr z
    by_cases hri : r ∈ Ioo a b
    · have he : (fun s ↦ value a b G s z) =ᶠ[𝓝 r] (fun s ↦ G s z) := by
        filter_upwards [Ioo_mem_nhds hri.1 hri.2] with s hs
        change G (clamp a b s) z = G s z
        rw [of_mem ⟨hs.1.le, hs.2.le⟩]
      simpa only [derivative, Set.indicator_of_mem hri] using (hd hri z).congr_of_eventuallyEq he
    · have hzero : derivative a b dG r z = 0 := Set.indicator_of_notMem hri _
      rw [hzero]
      rcases lt_or_gt_of_ne hra with hra | har
      · apply (hasDerivAt_const r (G a z)).congr_of_eventuallyEq
        filter_upwards [eventually_lt_nhds hra] with s hs
        change G (clamp a b s) z = G a z
        rw [of_le_left hab hs.le]
      · have hbr : b < r := lt_of_le_of_ne (not_lt.mp (fun h ↦ hri ⟨har, h⟩)) hrb.symm
        apply (hasDerivAt_const r (G b z)).congr_of_eventuallyEq
        filter_upwards [eventually_gt_nhds hbr] with s hs
        change G (clamp a b s) z = G b z
        rw [of_right_le hab hs.le]
  · exact hG.derivative_measurable.indicator (measurableSet_Ioo.preimage measurable_fst)
  · intro r
    change Continuous (fun z : State n ↦ (Ioo a b).indicator (fun r ↦ dG r z) r)
    by_cases hr : r ∈ Ioo a b
    · simpa only [derivative, Set.indicator_of_mem hr] using hG.derivative_state_continuous r
    · simpa only [derivative, Set.indicator_of_notMem hr] using (continuous_const : Continuous (fun _ : State n ↦ (0 : ℝ)))
  · obtain ⟨v, hv, hve⟩ := hG.derivative_envelope
    have hi : Integrable ((Ioo a b).indicator (fun r ↦ |v r|)) (volume : Measure ℝ) :=
      (integrable_indicator_iff measurableSet_Ioo).mpr (hv.abs.1.mono_set Ioo_subset_Ioc_self)
    refine ⟨(Ioo a b).indicator (fun r ↦ |v r|), hi.intervalIntegrable, ?_⟩
    intro r hr z
    by_cases hri : r ∈ Ioo a b
    · simpa only [derivative, Set.indicator_of_mem hri] using (hve r hri z).trans (le_abs_self _)
    · simp only [derivative, Set.indicator_of_notMem hri, norm_zero, le_refl]
  · obtain ⟨M, L, B, hb⟩ := hG.bounds
    exact ⟨M, L, B, fun r z ↦ hb (clamp a b r) z⟩

def constant (G : ℝ → State n → ℝ) (r : ℝ) (_ : ℝ) : State n → ℝ := G r

/-- A state test frozen at one time is a regular time-independent test. -/
theorem constant_regular (hG : RegularTest a b G dG) (r : ℝ) (H : ℝ≥0) :
    RegularTest 0 (H : ℝ) (constant G r) (fun _ _ ↦ 0) := by
  have hk : Continuous (fun p : ℝ × State n ↦ (r, p.2)) := continuous_const.prodMk continuous_snd
  refine
    { continuous := hG.continuous.comp hk
      state_smooth := fun _ ↦ hG.state_smooth r
      gradient_continuous := hG.gradient_continuous.comp hk
      hessian_continuous := hG.hessian_continuous.comp hk
      time_absolutelyContinuous := fun z ↦
        (LipschitzWith.const (G r z)).lipschitzOnWith.absolutelyContinuousOnInterval
      time_derivative := Filter.Eventually.of_forall (fun t ht z ↦ hasDerivAt_const t (G r z))
      derivative_measurable := measurable_const
      derivative_state_continuous := fun _ ↦ continuous_const
      derivative_envelope := ⟨fun _ ↦ 0, intervalIntegrable_const, fun _ _ _ ↦ by simp⟩
      bounds := ?_ }
  obtain ⟨M, L, B, hb⟩ := hG.bounds
  exact ⟨M, L, B, fun _ z ↦ hb r z⟩

end SHEStochastic.FiniteItoTestExtension
