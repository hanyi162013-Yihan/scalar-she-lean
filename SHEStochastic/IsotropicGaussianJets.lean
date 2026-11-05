module

public import SHEStochastic.IsotropicGaussianHolder
public import SHEStochastic.MatrixHaarScaling
public import SHE.GaussianRangeJetBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.IsotropicGaussianJets
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianConvolution
open SHE.GaussianRangeSmooth
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def constant (n k : ℕ) : ℝ := extensionJetConstant (1 : Matrix (Fin n) (Fin n) ℝ) k

theorem constant_nonneg (n k : ℕ) : 0 ≤ constant n k := extensionJetConstant_nonneg _ _

/-- Normalize the actual isotropic covariance by spatial dilation.
The Gaussian density and all its higher derivatives are reused at unit
variance, so no scale-dependent derivative constant is introduced. -/
theorem average_std {r : ℝ} (hr : 0 ≤ r) (F : State n → ℝ) (hF : Measurable F) (z : State n) :
    gaussianAverage (IsotropicGaussianHolder.matrix r) F z=
      ∫ y, F (z+Real.sqrt r • y) ∂stdGaussian (State n) := by
  have hs : CFC.sqrt (IsotropicGaussianHolder.matrix (n := n) r)=
      Real.sqrt r • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [IsotropicGaussianHolder.matrix,MatrixHaarScaling.sqrt_smul _ zero_le_one r hr,CFC.sqrt_one]
  have hm : Measurable (fun y : State n => F (z+y)) := hF.comp (measurable_const.add measurable_id)
  rw [gaussianAverage,multivariateGaussian,integral_map (by fun_prop) hm.aestronglyMeasurable]
  simp only [zero_add,hs,map_smul,map_one,ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply]

theorem normalized {r : ℝ} (hr : 0 < r) (F : State n → ℝ) (hF : Measurable F) (z : State n) :
    gaussianAverage (IsotropicGaussianHolder.matrix r) F z=
      roughAverageExtension (1 : Matrix (Fin n) (Fin n) ℝ)
        (fun y => F (Real.sqrt r • y)) ((Real.sqrt r)⁻¹ • z) := by
  have hz : (Real.sqrt r)⁻¹ • z ∈
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)).range := by
    refine ⟨(Real.sqrt r)⁻¹ • z,?_⟩
    simp
  rw [extension_eq_average_on_range _ _ hz,average_std hr.le F hF z,
    gaussianAverage,multivariateGaussian_zero_one]
  apply integral_congr_ae
  filter_upwards with y
  rw [smul_add,smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hr).ne',one_smul]

theorem smooth {r : ℝ} (hr : 0 < r) (F : State n → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) (k : ℕ) :
    ContDiff ℝ k (gaussianAverage (IsotropicGaussianHolder.matrix r) F) := by
  have he : gaussianAverage (IsotropicGaussianHolder.matrix r) F=
      roughAverageExtension (IsotropicGaussianHolder.matrix r) F := by
    funext z
    exact (extension_eq_average_on_range _ _ (by rw [IsotropicGaussianHolder.range_top hr.ne']; trivial)).symm
  rw [he]
  exact contDiff_roughAverageExtension (IsotropicGaussianHolder.nonnegative hr.le) F hF M hM k

/-- Every actual Frechet derivative order has the expected inverse
standard-deviation power, uniformly over all means and bounded tests. -/
theorem bound {r : ℝ} (hr : 0 < r) (F : State n → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) (k : ℕ) (z : State n) :
    ‖iteratedFDeriv ℝ k (gaussianAverage (IsotropicGaussianHolder.matrix r) F) z‖ ≤
      M*constant n k*((Real.sqrt r)⁻¹)^k := by
  let G : State n → ℝ := fun y => F (Real.sqrt r • y)
  let L : State n →L[ℝ] State n := (Real.sqrt r)⁻¹ • ContinuousLinearMap.id ℝ (State n)
  have hG : Measurable G := hF.comp (measurable_id.const_smul (Real.sqrt r))
  have hb : ∀ y, |G y| ≤ M := fun y => hM _
  have hs := contDiff_roughAverageExtension (Matrix.PosSemidef.one (n := Fin n)) G hG M hb k
  have he : gaussianAverage (IsotropicGaussianHolder.matrix r) F=
      roughAverageExtension (1 : Matrix (Fin n) (Fin n) ℝ) G ∘ L :=
    funext (normalized hr F hF)
  rw [he,L.iteratedFDeriv_comp_right hs z le_rfl]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hL : ‖L‖ ≤ (Real.sqrt r)⁻¹ := by
    have hi : ‖ContinuousLinearMap.id ℝ (State n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    dsimp only [L]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg r))]
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (Real.sqrt_nonneg r))).trans_eq (mul_one _)
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  exact mul_le_mul (norm_extension_jet Matrix.PosSemidef.one G hG hb k (L z))
    (pow_le_pow_left₀ (norm_nonneg _) hL k) (pow_nonneg (norm_nonneg L) _)
      (mul_nonneg hM0 (constant_nonneg n k))

end SHEStochastic.IsotropicGaussianJets
