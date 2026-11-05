module

public import SHEStochastic.IsotropicGaussianBands

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.IsotropicGaussianDyadicBands
open MeasureTheory SHE SHE.GaussianIncrement SHE.GaussianConvolution
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

def variance (j : ℕ) : ℝ := ((2 : ℝ)^j)⁻¹^2

theorem variance_pos (j : ℕ) : 0 < variance j := by unfold variance; positivity

theorem inverse_sqrt (j : ℕ) : (Real.sqrt (variance j))⁻¹=(2 : ℝ)^j := by
  rw [variance,Real.sqrt_sq (by positivity),inv_inv]

theorem four_next (j : ℕ) : 4*variance (j+1)=variance j := by
  unfold variance
  rw [show (2 : ℝ)^(j+1)=(2 : ℝ)^j*2 by rw [pow_succ],mul_inv_rev,mul_pow]
  norm_num
  ring

theorem variance_power (β : ℝ) (j : ℕ) : (variance j)^(β/2)=((2 : ℝ)^j)^(-β) := by
  unfold variance
  rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ ((2 : ℝ)^j)⁻¹) 2 (β/2)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ)*(β/2)=β by ring,Real.inv_rpow (by positivity) β,Real.rpow_neg (by positivity)]

theorem scaled_variance_power (β : ℝ) (j : ℕ) :
    (3*variance j)^(β/2)=3^(β/2)*((2 : ℝ)^j)^(-β) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (variance_pos j).le,variance_power]

/-- The vector Gaussian bands have the same dyadic amplitude and
frequency as the scalar comparison machinery already uses. -/
theorem uniform_jets {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (N k : ℕ) (hk : k ≤ N) (j : ℕ) (z : State n) :
    ‖iteratedFDeriv ℝ k (IsotropicGaussianBands.band (variance j) F) z‖ ≤
      (K*3^(β/2)*GaussianNormMoment.moment (Fin n) β*IsotropicGaussianBands.finiteConstant n N)*
        ((2 : ℝ)^j)^(-β)*((2 : ℝ)^j)^k := by
  have h := IsotropicGaussianBands.uniform_jets (variance_pos j) hK hβ F hF M hM hH N k hk z
  rw [scaled_variance_power,inverse_sqrt] at h
  exact h.trans_eq (by ring)

/-- Exact finite reconstruction, before any limit or regularity
argument. Only the initial low band remains outside the finite sum. -/
theorem telescope (F : State n → ℝ) (N : ℕ) (z : State n) :
    gaussianAverage (IsotropicGaussianHolder.matrix 1) F z+
      ∑ j ∈ Finset.range N, IsotropicGaussianBands.band (variance (j+1)) F z=
        gaussianAverage (IsotropicGaussianHolder.matrix (variance N)) F z := by
  induction N with
  | zero => simp [variance]
  | succ N ih =>
    rw [Finset.sum_range_succ,← add_assoc,ih]
    unfold IsotropicGaussianBands.band
    rw [four_next]
    ring

/-- The actual rough vector coefficient is recovered uniformly, with
the same decaying dyadic Holder amplitude used in the finite estimates. -/
theorem remainder {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (N : ℕ) (z : State n) :
    |F z-(gaussianAverage (IsotropicGaussianHolder.matrix 1) F z+
      ∑ j ∈ Finset.range N, IsotropicGaussianBands.band (variance (j+1)) F z)| ≤
        K*((2 : ℝ)^N)^(-β)*GaussianNormMoment.moment (Fin n) β := by
  rw [telescope,abs_sub_comm]
  have h := IsotropicGaussianBands.displacement (variance_pos N).le hK hβ F hF M hM hH z
  rwa [variance_power] at h

end SHEStochastic.IsotropicGaussianDyadicBands
