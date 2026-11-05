module

public import SHE.GaussianItoTest
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-! Actual all-order smooth bounded cylinder calculus. This supplies the
smooth-cutoff class in which physical covariance insertions can iterate. -/
noncomputable section
namespace SHE.SmoothCylinders
open Set MeasureTheory ProbabilityTheory GaussianSmooth
open scoped ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- All bounds are on genuine Fréchet derivatives, including order zero. -/
structure BoundedSmooth (F : E → G) : Prop where
  smooth : ContDiff ℝ ∞ F
  bounds : ∀ k : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ k F z‖ ≤ M

namespace BoundedSmooth

theorem norm_bound {F : E → G} (hF : BoundedSmooth F) : ∃ M : ℝ, ∀ z, ‖F z‖ ≤ M := by
  simpa only [norm_iteratedFDeriv_zero] using hF.bounds 0

theorem fderiv {F : E → G} (hF : BoundedSmooth F) : BoundedSmooth (fderiv ℝ F) := by
  refine ⟨hF.smooth.fderiv_right (by simp), fun k => ?_⟩
  obtain ⟨M, hM⟩ := hF.bounds (k + 1)
  exact ⟨M, fun z => by simpa only [norm_iteratedFDeriv_fderiv] using hM z⟩

theorem hessian_norm_bound {F : E → ℝ} (hF : BoundedSmooth F) :
    ∃ B : ℝ, ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B := hF.fderiv.fderiv.norm_bound

end BoundedSmooth

section Average
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem contDiff_average_nat (μ : Measure E) [IsProbabilityMeasure μ]
    (k : ℕ) {F : E → G} (hF : BoundedSmooth F) : ContDiff ℝ k (average μ F) := by
  induction k generalizing G with
  | zero =>
    obtain ⟨M, hM⟩ := hF.norm_bound
    exact contDiff_zero.mpr (continuous_average μ hF.smooth.continuous hM)
  | succ k ih =>
    obtain ⟨M, hM⟩ := hF.norm_bound
    obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
    have hF1 : ContDiff ℝ 1 F := hF.smooth.of_le (by simp)
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun z => (hasFDerivAt_average μ hF1 hM hL z).differentiableAt, by simp, ?_⟩
    rw [fderiv_average μ hF1 hM hL]
    exact ih hF.fderiv

theorem norm_iteratedFDeriv_average_le (μ : Measure E) [IsProbabilityMeasure μ]
    (k : ℕ) {F : E → G} (hF : BoundedSmooth F) {M : ℝ}
    (hM : ∀ z, ‖iteratedFDeriv ℝ k F z‖ ≤ M) (z : E) :
    ‖iteratedFDeriv ℝ k (average μ F) z‖ ≤ M := by
  induction k generalizing G with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact average_norm_bound μ (fun z => by simpa only [norm_iteratedFDeriv_zero] using hM z) z
  | succ k ih =>
    obtain ⟨M₀, hM₀⟩ := hF.norm_bound
    obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
    rw [← norm_iteratedFDeriv_fderiv (n := k),
      fderiv_average μ (hF.smooth.of_le (by simp)) hM₀ hL]
    exact ih hF.fderiv (fun z => by simpa only [norm_iteratedFDeriv_fderiv] using hM z)

theorem BoundedSmooth.average (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E → G} (hF : BoundedSmooth F) : BoundedSmooth (GaussianSmooth.average μ F) := by
  refine ⟨contDiff_infty.mpr (fun k => contDiff_average_nat μ k hF), fun k => ?_⟩
  obtain ⟨M, hM⟩ := hF.bounds k
  exact ⟨M, norm_iteratedFDeriv_average_le μ k hF hM⟩

end Average
end SHE.SmoothCylinders
