module

public import SHE.UniformProfileReserve
public import SHE.GaussianBorelMovingMean
public import SHE.GaussianBorelPathLipschitz
public import SHE.LipschitzIntegralIdentity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth.ProfileReserve
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianProfileMark GaussianConvolution
open scoped NNReal Matrix.Norms.L2Operator Topology
variable {n : ℕ} {A : ℝ → Mat n}

theorem exists_lipschitz_fixed_mean (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n) :
    ∃ L : ℝ≥0, LipschitzWith L (fun θ => gaussianAverage (A θ) F z) := by
  have hh := exists_lipschitz_borel_reserve Q.floor_positive Q.residual hK Q.residual_range F hF M hM z
  simpa only [← Q.covariance_eq] using hh

/-- The marked a.e. derivative gives an exact endpoint identity, with
interval integrability derived from the actual reserve/Lipschitz proof. -/
theorem integral_fixed_mean (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n)
    (mark : ℝ → ℝ)
    (hmark : ∀ᵐ θ ∂volume, HasDerivAt (fun s => gaussianAverage (A s) F z) (mark θ) θ)
    (a b : ℝ) : IntervalIntegrable mark volume a b ∧
      (∫ θ in a..b, mark θ) = gaussianAverage (A b) F z - gaussianAverage (A a) F z := by
  obtain ⟨L, hL⟩ := exists_lipschitz_fixed_mean Q hK F hF M hM z
  exact LipschitzIntegralIdentity.integral_eq_sub hL hmark a b

/-- The affine physical-mean/covariance diagonal has the genuine sum of
the two proved partial derivatives. Range membership is needed only for
the mean direction, never for the base mean. -/
theorem hasDerivAt_affine_of_partials (Q : ProfileReserve A) {K : ℝ≥0}
    (hK : LipschitzWith K (fun θ => (Q.residual θ).val))
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (base d : State n) {θ a b : ℝ}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A θ)).range)
    (hcov : HasDerivAt (fun s => gaussianAverage (A s) F (base + θ • d)) a θ)
    (hmean : HasDerivAt (fun r : ℝ => gaussianAverage (A θ) F (base + θ • d + r • d)) b 0) :
    HasDerivAt (fun s => gaussianAverage (A s) F (base + s • d)) (a + b) θ := by
  have hdr : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) Q.floor).range := by simpa only [Q.full_range θ] using hd
  have hm : HasDerivAt (fun s : ℝ => base + s • d) d θ := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id θ).smul_const d).const_add base
  have hmr (s : ℝ) : base + s • d - base ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) Q.floor).range := by
    rw [add_sub_cancel_left]
    exact Submodule.smul_mem _ s hdr
  have hc : ContinuousAt Q.residual θ := tendsto_subtype_rng.mpr hK.continuous.continuousAt
  have hcov' : HasDerivAt (fun s => gaussianAverage (Q.floor + (Q.residual s).val) F (base + θ • d)) a θ := by
    simpa only [← Q.covariance_eq] using hcov
  have hmean' : HasDerivAt (fun r : ℝ => gaussianAverage (Q.floor + (Q.residual θ).val) F (base + θ • d + r • d)) b 0 := by
    simpa only [← Q.covariance_eq] using hmean
  have hh := hasDerivAt_borel_moving_mean_of_partials Q.floor_positive Q.residual hc Q.residual_range
    (fun s : ℝ => base + s • d) hm base hmr hdr F hF M hM hcov' hmean'
  simpa only [← Q.covariance_eq] using hh

end SHE.GaussianRangeSmooth.ProfileReserve
