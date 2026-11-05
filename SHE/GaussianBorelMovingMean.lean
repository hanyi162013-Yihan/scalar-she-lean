module

public import SHE.GaussianMovingMean
public import SHE.GaussianReserveAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! The genuine diagonal chain rule for bounded Borel Gaussian tests.
The fixed reserve provides uniform Taylor control in physical directions,
so separate covariance and mean partial derivatives combine legitimately. -/
namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianContinuity
  MeasurableGeneralizedInverse
open scoped MatrixOrder Matrix.Norms.L2Operator Topology
variable {n : ℕ}

theorem hasDerivAt_borel_moving_mean_of_partials
    {R : Mat n} (hR : R.PosSemidef) (C : ℝ → PositiveCovariance n) {θ a b : ℝ}
    (hC : ContinuousAt C θ)
    (hrange : ∀ s, (Matrix.toEuclideanCLM (𝕜 := ℝ) (C s).val).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (m : ℝ → State n) {d : State n} (hm : HasDerivAt m d θ) (base : State n)
    (hmrange : ∀ s, m s - base ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (hdrange : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hcov : HasDerivAt (fun s => gaussianAverage (R + (C s).val) F (m θ)) a θ)
    (hmean : HasDerivAt (fun r : ℝ => gaussianAverage (R + (C θ).val) F (m θ + r • d)) b 0) :
    HasDerivAt (fun s => gaussianAverage (R + (C s).val) F (m s)) (a + b) θ := by
  let F₀ : State n → ℝ := fun y => F (base + y)
  let H := roughAverageExtension R F₀
  let m₀ : ℝ → State n := fun s => m s - base
  have hFm : Measurable F₀ := hF.comp (measurable_const.add measurable_id)
  have hFb : ∀ y, |F₀ y| ≤ M := fun y => hM _
  obtain ⟨hH, hH0, hH1, hH2, _, _⟩ := extension_covariance_regularity hR F₀ hFm hFb
  have he (s : ℝ) (z : State n) (hz : z ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range) :
      gaussianAverage (C s).val H z = gaussianAverage (R + (C s).val) F (base + z) := by
    have hh := reserve_average hR (C s).property (hrange s) F₀ hFm M hFb hz
    rw [hh]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by simp only [F₀]; rw [add_assoc])
  have hc : HasDerivAt (fun s => gaussianAverage (C s).val H (m₀ θ)) a θ := by
    have hfuneq : (fun s => gaussianAverage (C s).val H (m₀ θ)) =
        fun s => gaussianAverage (R + (C s).val) F (m θ) := by
      funext s
      rw [he s (m₀ θ) (hmrange θ)]
      congr 1
      dsimp [m₀]
      abel
    rw [hfuneq]
    exact hcov
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  have hB : 0 ≤ M * extensionJetConstant R 2 := mul_nonneg hM0 (extensionJetConstant_nonneg R 2)
  have hd := GaussianMovingMean.hasDerivAt_moving_mean_of_partial C hC m₀ (hm.sub_const base)
    hc hH hH0 hH1 hH2 hB
  have hline : HasDerivAt (fun r : ℝ => m₀ θ + r • d) d 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (m₀ θ)
  have hcH := GaussianSmooth.contDiff_average_two (multivariateGaussian 0 (C θ).val) hH hH0 hH1 hH2
  have hl := ((hcH.differentiable (by norm_num)) (m₀ θ + (0 : ℝ) • d)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  change HasDerivAt (fun r : ℝ => GaussianSmooth.average (multivariateGaussian 0 (C θ).val) H (m₀ θ + r • d))
    (fderiv ℝ (GaussianSmooth.average (multivariateGaussian 0 (C θ).val) H) (m₀ θ + (0 : ℝ) • d) d) 0 at hl
  simp only [zero_smul, add_zero] at hl
  have hlineeq : (fun r : ℝ => GaussianSmooth.average (multivariateGaussian 0 (C θ).val) H (m₀ θ + r • d)) =
      fun r : ℝ => gaussianAverage (R + (C θ).val) F (m θ + r • d) := by
    funext r
    change gaussianAverage (C θ).val H (m₀ θ + r • d) = _
    rw [he θ _ (Submodule.add_mem _ (hmrange θ) (Submodule.smul_mem _ r hdrange))]
    congr 1
    change base + (m θ - base + r • d) = m θ + r • d
    abel
  rw [hlineeq] at hl
  have hb : fderiv ℝ (gaussianAverage (C θ).val H) (m₀ θ) d = b := by
    have heq : gaussianAverage (C θ).val H = GaussianSmooth.average (multivariateGaussian 0 (C θ).val) H := rfl
    rw [heq]
    exact hl.unique hmean
  rw [hb] at hd
  have hdiag : (fun s => gaussianAverage (C s).val H (m₀ s)) =
      fun s => gaussianAverage (R + (C s).val) F (m s) := by
    funext s
    rw [he s (m₀ s) (hmrange s)]
    congr 1
    dsimp [m₀]
    abel
  rw [hdiag] at hd
  exact hd

end SHE.GaussianRangeSmooth
