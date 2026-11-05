module

public import SHE.ScalarHeatBands
public import SHE.ScalarGaussianJetScale

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ScalarHeatBandJets
open Set MeasureTheory ProbabilityTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup ScalarGaussianJetScale ScalarHeatBands
open scoped NNReal ENNReal

/-- Every actual Gaussian-heat band has its precise positive-order
Holder/Bernstein scale, uniformly in the unsmoothed derivative bounds. -/
theorem positive_jet {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j n : ℕ) (x : ℝ) :
    |iteratedDeriv (n+1) (band a j) x|≤
      2*H*constant β n*CompactMollifier.radius j^(β-(n:ℝ)-1) := by
  have hc : 0≤H*constant β n:=mul_nonneg hH (constant_nonneg β n)
  have hs (l : ℕ) : |iteratedDeriv (n+1) (smooth a l) x|≤
      H*constant β n*CompactMollifier.radius l^(β-(n:ℝ)-1):=by
    simpa only [smooth,variance_power] using
      jet_holder (variance l) (variance_pos l).ne' ha hH hβ hh n x
  cases j with
  | zero =>
    change |iteratedDeriv (n+1) (smooth a 0) x|≤_
    exact (hs 0).trans (by nlinarith [mul_nonneg hc (rpow_nonneg (CompactMollifier.radius_pos 0).le (β-(n:ℝ)-1))])
  | succ j =>
    change |iteratedDeriv (n+1) (smooth a (j+1)-smooth a j) x|≤_
    rw [iteratedDeriv_sub
      ((smooth_boundedSmooth ha (j+1)).smooth.of_le (by simp)).contDiffAt
      ((smooth_boundedSmooth ha j).smooth.of_le (by simp)).contDiffAt]
    have hr : CompactMollifier.radius j^(β-(n:ℝ)-1)≤CompactMollifier.radius (j+1)^(β-(n:ℝ)-1):=
      Real.rpow_le_rpow_of_nonpos (CompactMollifier.radius_pos (j+1)) (ScalarDyadicBands.radius_antitone j)
        (by have hn : 0≤(n:ℝ):=Nat.cast_nonneg n; linarith)
    exact (abs_sub _ _).trans ((add_le_add (hs (j+1))
      ((hs j).trans (mul_le_mul_of_nonneg_left hr hc))).trans_eq (by ring))

/-- An arbitrary additional future Gaussian variance preserves the
small-scale band bound on the actual derivative. -/
theorem heated_positive_jet {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ : ℝ≥0) (j n : ℕ) (x : ℝ) :
    |iteratedDeriv (n+1) (heat σ (band a j)) x|≤
      2*H*constant β n*CompactMollifier.radius j^(β-(n:ℝ)-1) := by
  rw [iteratedDeriv_heat σ (band_boundedSmooth ha j) (n+1)]
  exact heat_bound σ (positive_jet ha hH hβ hβ1 hh j n) x

end SHE.ScalarHeatBandJets
