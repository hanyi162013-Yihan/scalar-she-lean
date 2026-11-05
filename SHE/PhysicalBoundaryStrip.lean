module

public import SHE.PhysicalRemainderMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual terminal boundary strips of a fixed physical insertion word.
The estimate is independent of heat target gaps and covariance rank.
It does not claim uniformity for tests whose derivatives themselves
depend on a vanishing cutoff. -/
noncomputable section
namespace SHE.PhysicalBoundaryStrip
open Set MeasureTheory ProbabilityTheory Filter StoppedFourier
open WordRecursion CovarianceEndpoint GaussianItoTest PhysicalIto PhysicalRemainderBound PhysicalRemainderMass
abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def strip {n : ℕ} (W : EndpointWindow n) (a : ℝ → ℝ)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) (F : State n → ℝ) (δ : ℝ) : ℝ :=
  ∫ t in max W.left (W.right-δ)..W.right,
    ∫ x, insertedWord W a U X F t x ∂AddCircle.haarAddCircle

theorem strip_norm_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hB : 0 ≤ B)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖strip W a U X F δ‖ ≤ ((1 / 2 : ℝ) * (A + W.upper) * B * n) * heatMass δ := by
  let q := max W.left (W.right-δ)
  let K : ℝ := (1 / 2 : ℝ) * (A + W.upper) * B * n
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA W.upper_nonneg)) hB) (Nat.cast_nonneg _)
  have hq : q ≤ W.right := max_le W.ordered (by linarith)
  have hleft : W.left ≤ q := le_max_left _ _
  have hlen : 0 ≤ W.right-q := sub_nonneg.mpr hq
  have hlenδ : W.right-q ≤ δ := by dsimp [q]; linarith [le_max_right W.left (W.right-δ)]
  have he : ‖strip W a U X F δ‖ ≤ ∫ t in q..W.right,
      K * (1 + heatConstant * (W.right-t)^(-(1/2:ℝ))) := by
    unfold strip
    apply intervalIntegral.norm_integral_le_of_norm_le hq ?_ (endpoint_majorant_integrable K)
    filter_upwards [volume.ae_ne W.right] with t htr ht
    have htW : t ∈ Ioo W.left W.right := ⟨hleft.trans_lt ht.1,lt_of_le_of_ne ht.2 htr⟩
    exact inserted_spatial_norm_bound W hA ha hB U X htW (backward W F t)
      (fun z => BackwardRegularity.gaussian_state_hessian_bound _ hF hbound hD hDD z)
  calc
    _ ≤ ∫ t in q..W.right, K * (1 + heatConstant * (W.right-t)^(-(1/2:ℝ))) := he
    _ = K * heatMass (W.right-q) := by
      rw [intervalIntegral.integral_const_mul,heat_majorant_mass hq]
      rfl
    _ ≤ K * heatMass δ := mul_le_mul_of_nonneg_left (heatMass_mono hlen hlenδ) hK

end SHE.PhysicalBoundaryStrip
