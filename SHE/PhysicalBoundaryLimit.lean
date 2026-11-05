module

public import SHE.PhysicalBoundaryStrip

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Removing a terminal time cutoff for a fixed smooth physical word.
The derivative bounds belong to that fixed test and are explicit. -/
noncomputable section
namespace SHE.PhysicalBoundaryStrip
open Set MeasureTheory Filter StoppedFourier
open WordRecursion CovarianceEndpoint GaussianItoTest PhysicalRemainderMass
open scoped Topology

theorem continuous_heatMass : Continuous heatMass := by
  unfold heatMass
  fun_prop

theorem strip_tendsto_zero {n : ℕ} (W : EndpointWindow n) {a : ℝ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hB : 0 ≤ B)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    {F : WordRecursion.State n → ℝ} (hF : ContDiff ℝ 2 F) {M L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) :
    Tendsto (fun δ => strip W a U X F δ) (𝓝[≥] 0) (𝓝 0) := by
  have hh : Tendsto (fun δ => ((1 / 2 : ℝ) * (A + W.upper) * B * n) * heatMass δ)
      (𝓝[≥] 0) (𝓝 0) := by
    have he := ((continuous_const (y := (1 / 2 : ℝ) * (A + W.upper) * B * n)).mul
      continuous_heatMass).tendsto (0 : ℝ)
    have he' := he.mono_left (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
    change Tendsto (fun δ => ((1 / 2 : ℝ) * (A + W.upper) * B * n) * heatMass δ)
      (𝓝[≥] 0) (𝓝 (((1 / 2 : ℝ) * (A + W.upper) * B * n) * heatMass 0)) at he'
    simpa only [Pi.mul_apply,heatMass, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0),mul_zero,zero_add,add_zero] using he'
  apply squeeze_zero_norm' ?_ hh
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact strip_norm_bound W hA ha hB U X hF hbound hD hDD hδ

end SHE.PhysicalBoundaryStrip
