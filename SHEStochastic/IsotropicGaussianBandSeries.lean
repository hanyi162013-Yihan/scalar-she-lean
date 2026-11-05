module

public import SHEStochastic.IsotropicGaussianDyadicBands
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.IsotropicGaussianBandSeries
open MeasureTheory Filter SHE SHE.GaussianIncrement SHE.GaussianConvolution
open IsotropicGaussianDyadicBands
open scoped Topology
variable {n : ℕ}

theorem geometric (β : ℝ) (j : ℕ) : ((2 : ℝ)^j)^(-β)=((2 : ℝ)^(-β))^j := by
  rw [←Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),mul_comm (j : ℝ),Real.rpow_mul_natCast (by norm_num)]

theorem decay {β : ℝ} (hβ : 0 < β) (C : ℝ) :
    Tendsto (fun j : ℕ => C*((2 : ℝ)^j)^(-β)) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-β))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hβ))
  simpa only [←geometric,mul_zero] using h.const_mul C

/-- Finite vector Gaussian band sums recover the original bounded
Holder function uniformly on the entire state space. -/
theorem uniform_reconstruction {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ z, |F z| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j ≥ N, ∀ z : State n,
      |F z-(gaussianAverage (IsotropicGaussianHolder.matrix 1) F z+
        ∑ l ∈ Finset.range j, IsotropicGaussianBands.band (variance (l+1)) F z)| < ε := by
  have h := decay hβ (K*GaussianNormMoment.moment (Fin n) β)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp h).2 ε hε)
  refine ⟨N,fun j hj z => ?_⟩
  exact (remainder hK hβ.le F hF M hM hH j z).trans_lt (by
    calc
      _ = K*GaussianNormMoment.moment (Fin n) β*((2 : ℝ)^j)^(-β) := by ring
      _ < ε := hN j hj)

/-- The reconstruction also converges at every actual state argument;
this is the limit used after bounds uniform in the dyadic cut-off. -/
theorem tendsto_reconstruction {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ z, |F z| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (z : State n) :
    Tendsto (fun N : ℕ => gaussianAverage (IsotropicGaussianHolder.matrix 1) F z+
      ∑ j ∈ Finset.range N, IsotropicGaussianBands.band (variance (j+1)) F z) atTop (𝓝 (F z)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := uniform_reconstruction hK hβ F hF M hM hH hε
  exact ⟨N,fun j hj => by simpa only [Real.dist_eq,abs_sub_comm] using hN j hj z⟩

/-- The original Holder coefficient has an absolutely summable vector
Gaussian band expansion, uniformly bounded by one geometric sequence. -/
theorem summable {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ z, |F z| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (z : State n) :
    Summable (fun j : ℕ => IsotropicGaussianBands.band (variance (j+1)) F z) := by
  let q : ℝ := 2^(-β)
  let C := K*3^(β/2)*GaussianNormMoment.moment (Fin n) β*IsotropicGaussianBands.finiteConstant n 0
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hβ)
  have hs : Summable (fun j : ℕ => (C*q)*q^j) :=
    (summable_geometric_of_norm_lt_one (x := q) (by rwa [Real.norm_eq_abs,abs_of_nonneg hq0])).mul_left (C*q)
  apply Summable.of_norm_bounded (f := fun j => IsotropicGaussianBands.band (variance (j+1)) F z) hs
  intro j
  have h := uniform_jets hK hβ.le F hF M hM hH 0 0 le_rfl (j+1) z
  simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at h
  rw [geometric β (j+1),pow_succ] at h
  exact h.trans_eq (by dsimp [C,q]; ring)

theorem reconstruction {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ z, |F z| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (z : State n) :
    F z=gaussianAverage (IsotropicGaussianHolder.matrix 1) F z+
      ∑' j : ℕ, IsotropicGaussianBands.band (variance (j+1)) F z := by
  exact tendsto_nhds_unique (tendsto_reconstruction hK hβ F hF M hM hH z)
    (((summable hK hβ F hF M hM hH z).hasSum.tendsto_sum_nat).const_add _)

end SHEStochastic.IsotropicGaussianBandSeries
