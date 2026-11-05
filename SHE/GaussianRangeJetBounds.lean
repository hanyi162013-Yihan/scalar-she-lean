module

public import SHE.GaussianRangeSmooth
public import SHE.GaussianLaplaceJets

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Uniform derivative bounds for the actual bounded-Borel Gaussian
range smoother. The constants involve only the fixed covariance and
genuine Gaussian moments; no derivatives of the rough test occur. -/
namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement
  MeasurableGeneralizedInverse GaussianConvolution
open scoped InnerProductSpace
variable {n : ℕ}

def zeroTilt (A : Mat n) (a : State n) : ℝ :=
  exp (-(inner ℝ a (Matrix.toEuclideanCLM (𝕜 := ℝ) A a)) / 2)

theorem contDiff_zeroTilt (A : Mat n) (k : ℕ) : ContDiff ℝ k (zeroTilt A) := by
  exact ((contDiff_id.inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).contDiff).neg.div_const 2).exp

def jetConstant (A : Mat n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (zeroTilt A) 0‖ *
    (∫ y : State n, ‖y‖ ^ (k - i) ∂multivariateGaussian 0 A)

theorem jetConstant_nonneg (A : Mat n) (k : ℕ) : 0 ≤ jetConstant A k := by
  unfold jetConstant
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (integral_nonneg (fun y => pow_nonneg (norm_nonneg y) _)))

theorem norm_lifted_jet_zero {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (liftedAverage A F) 0‖ ≤ M * jetConstant A k := by
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  have hb : ∀ y, ‖F y‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM
  have hb' : ∀ y, ‖F y‖ ≤ M * exp (0 * ‖y‖) := by simpa using hb
  have hl := GaussianLaplaceSmooth.contDiff_transform k (multivariateGaussian 0 A)
    hF.stronglyMeasurable hM0 hb'
  have he : liftedAverage A F = fun a => zeroTilt A a *
      GaussianLaplaceSmooth.transform (multivariateGaussian 0 A) F a :=
    funext (liftedAverage_likelihood hA F hF M hM)
  rw [he]
  apply (norm_iteratedFDeriv_mul_le (contDiff_zeroTilt A k) hl 0 le_rfl).trans
  unfold jetConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := GaussianLaplaceSmooth.norm_iterated_zero_bounded (k - i)
    (multivariateGaussian 0 A) hF.stronglyMeasurable hM0 hb
  have hm := mul_le_mul_of_nonneg_left hi
    (mul_nonneg (Nat.cast_nonneg (k.choose i)) (norm_nonneg (iteratedFDeriv ℝ i (zeroTilt A) 0)))
  convert! hm using 1
  ring

/-- Every derivative order has a global bound independent of the mean.
The test can be bounded Borel and the covariance can be singular. -/
theorem norm_lifted_jet {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M)
    (k : ℕ) (a : State n) :
    ‖iteratedFDeriv ℝ k (liftedAverage A F) a‖ ≤ M * jetConstant A k := by
  let Fa : State n → ℝ := fun y => F (Matrix.toEuclideanCLM (𝕜 := ℝ) A a + y)
  have hm : Measurable Fa := hF.comp (measurable_const.add measurable_id)
  have hb : ∀ y, |Fa y| ≤ M := fun y => hM _
  have he : (fun x => liftedAverage A F (a + x)) = liftedAverage A Fa := by
    funext x
    unfold liftedAverage gaussianAverage Fa
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change F (Matrix.toEuclideanCLM (𝕜 := ℝ) A (a + x) + y) =
      F (Matrix.toEuclideanCLM (𝕜 := ℝ) A a + (Matrix.toEuclideanCLM (𝕜 := ℝ) A x + y))
    rw [map_add, add_assoc]
  have hh := norm_lifted_jet_zero hA Fa hm hb k
  rw [← he, iteratedFDeriv_comp_add_left, add_zero] at hh
  exact hh

def extensionJetConstant (A : Mat n) (k : ℕ) : ℝ :=
  jetConstant A k * ‖(generalizedInverse A).toContinuousLinearMap‖ ^ k

theorem extensionJetConstant_nonneg (A : Mat n) (k : ℕ) : 0 ≤ extensionJetConstant A k :=
  mul_nonneg (jetConstant_nonneg A k) (pow_nonneg (norm_nonneg _) _)

theorem norm_extension_jet {A : Mat n} (hA : A.PosSemidef)
    (F : State n → ℝ) (hF : Measurable F) {M : ℝ} (hM : ∀ y, |F y| ≤ M)
    (k : ℕ) (z : State n) :
    ‖iteratedFDeriv ℝ k (roughAverageExtension A F) z‖ ≤ M * extensionJetConstant A k := by
  let G := (generalizedInverse A).toContinuousLinearMap
  change ‖iteratedFDeriv ℝ k (liftedAverage A F ∘ G) z‖ ≤ _
  rw [G.iteratedFDeriv_comp_right (contDiff_liftedAverage hA F hF M hM k) z le_rfl]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hi := mul_le_mul_of_nonneg_right (norm_lifted_jet hA F hF hM k (G z))
    (pow_nonneg (norm_nonneg G) k)
  unfold extensionJetConstant
  change _ ≤ M * (jetConstant A k * ‖G‖ ^ k)
  simpa only [mul_assoc] using hi

end SHE.GaussianRangeSmooth
