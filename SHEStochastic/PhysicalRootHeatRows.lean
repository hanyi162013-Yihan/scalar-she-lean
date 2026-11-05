module

public import SHEStochastic.NativePhysicalObservationInput
public import SHEStochastic.HolderStateRows
public import SHE.NonlinearHaarIntegrand

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.PhysicalRootHeatRows
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

theorem push_test {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) :
    NativePhysicalState.push (ScalarHaarHeatRows.test τ x) =ᵐ[haarAddCircle]
      RealCausalHeatKernel.value x τ := by
  have he : NativeHeatObservation.embed (ScalarHaarHeatRows.test τ x) = circleHeat τ x := by
    rw [NativeHeatObservation.embed_apply, ScalarHaarHeatRows.embed_test hτ,
      LinearIsometryEquiv.apply_symm_apply]
  have hc := NativePhysicalState.embed_eq_push (ScalarHaarHeatRows.test τ x)
  rw [he] at hc
  have hk := (NativeHeatSpan.kernel_physical_ae hτ x).trans (ProfileVariance.heatPhysical_ae hτ x)
  filter_upwards [hc, hk] with y hy hk
  have hh := congrArg Complex.re (hy.symm.trans hk.symm)
  simpa only [RealCausalHeatKernel.complex_eq hτ, Complex.ofReal_re] using hh

theorem push_action {ell cap : ℝ} (hell : 0 < ell) (f : EllipticField ell cap) (v : RealL2) :
    NativePhysicalState.push (RealRootMultiplier.action hell f v) =ᵐ[haarAddCircle]
      fun y ↦ Real.sqrt (CircleNormalization.push f.1 y).re * NativePhysicalState.push v y := by
  have hr := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae
    (RealRootMultiplier.action_ae hell f v)
  filter_upwards [NativePhysicalState.push_ae (RealRootMultiplier.action hell f v), hr,
    CircleNormalization.push_ae f.1, NativePhysicalState.push_ae v] with y hp hr hf hv
  rw [hp, hr, hf, hv]

theorem coefficient_action {a G : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ}
    (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hsquare : ∀ z, a z = (G z)^2) (hGpos : ∀ z, 0 ≤ G z) (u v : RealL2) :
    NativePhysicalState.push (RealRootMultiplier.action hell
      (NonlinearHaarIntegrand.coefficientField a ha ell cap hell hb u) v) =ᵐ[haarAddCircle]
        fun y ↦ G (NativePhysicalState.push u y) * NativePhysicalState.push v y := by
  have hc := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae
    (CoefficientFields.coefficient_ae a ha cap (NonlinearHaarIntegrand.absBound hell hb) u)
  filter_upwards [push_action hell (NonlinearHaarIntegrand.coefficientField a ha ell cap hell hb u) v,
    CircleNormalization.push_ae (NonlinearHaarIntegrand.coefficientField a ha ell cap hell hb u).1,
    hc, NativePhysicalState.push_ae u] with y hp hf hc hu
  change (NonlinearHaarIntegrand.coefficientField a ha ell cap hell hb u).1
    (CircleNormalization.scale (2 * Real.pi) 1 y) = _ at hc
  rw [hp, hf, hc, Complex.ofReal_re, hsquare, Real.sqrt_sq (hGpos _), ← hu]

/-- The physical innovation gives precisely the literal scalar
coefficient times the heat kernel used by the native weak equation. -/
theorem coefficient_heat {a G : ℝ → ℝ} (ha : Measurable a) {ell cap : ℝ}
    (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hsquare : ∀ z, a z = (G z)^2) (hGpos : ∀ z, 0 ≤ G z)
    (u : RealL2) {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) :
    NativePhysicalState.push (RealRootMultiplier.action hell
      (NonlinearHaarIntegrand.coefficientField a ha ell cap hell hb u)
        (ScalarHaarHeatRows.test τ x)) =ᵐ[haarAddCircle]
      fun y ↦ RealCausalHeatKernel.value x τ y * G (NativePhysicalState.push u y) := by
  filter_upwards [coefficient_action ha hell hb hsquare hGpos u (ScalarHaarHeatRows.test τ x),
    push_test hτ x] with y hp ht
  rw [hp, ht, mul_comm]

end SHEStochastic.PhysicalRootHeatRows
