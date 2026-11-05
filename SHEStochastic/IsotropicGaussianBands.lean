module

public import SHEStochastic.IsotropicGaussianJets
public import SHEStochastic.BanachGaussianDisplacement
public import SHEStochastic.MatrixOrthogonalField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.IsotropicGaussianBands
open MeasureTheory ProbabilityTheory SHE SHE.GaussianIncrement SHE.GaussianConvolution
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def band (r : ℝ) (F : State n → ℝ) (z : State n) : ℝ :=
  gaussianAverage (IsotropicGaussianHolder.matrix r) F z-
    gaussianAverage (IsotropicGaussianHolder.matrix (4*r)) F z

theorem covariance_norm {r : ℝ} (hr : 0 ≤ r) : ‖IsotropicGaussianHolder.matrix (n := n) r‖ ≤ r := by
  rw [IsotropicGaussianHolder.matrix,norm_smul,Real.norm_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left (MatrixOrthogonalField.matrix_norm _ (by simp)) hr).trans_eq (mul_one _)

theorem average_bound (A : Matrix (Fin n) (Fin n) ℝ) (F : State n → ℝ)
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n) : |gaussianAverage A F z| ≤ M := by
  simpa only [Real.norm_eq_abs,GaussianSmooth.average,gaussianAverage] using
    GaussianSmooth.average_norm_bound (multivariateGaussian (0 : State n) A) (F := F) (M := M)
      (by simpa only [Real.norm_eq_abs] using hM) z

theorem displacement {r K β : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (z : State n) :
    |gaussianAverage (IsotropicGaussianHolder.matrix r) F z-F z| ≤
      K*r^(β/2)*GaussianNormMoment.moment (Fin n) β := by
  simpa only [Real.norm_eq_abs,gaussianAverage] using BanachGaussianDisplacement.bound F hF.stronglyMeasurable M
    (by simpa only [Real.norm_eq_abs] using hM) hK hβ
    (by simpa only [Real.norm_eq_abs] using hH) (IsotropicGaussianHolder.matrix r)
    (IsotropicGaussianHolder.nonnegative hr).nonneg hr (covariance_norm hr) z

/-- A band is a single positive-scale smoother applied to a small
Holder increment. This supplies the amplitude before differentiating. -/
theorem identity {r : ℝ} (hr : 0 < r) (F : State n → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) :
    band r F=gaussianAverage (IsotropicGaussianHolder.matrix r)
      (fun z => F z-gaussianAverage (IsotropicGaussianHolder.matrix (3*r)) F z) := by
  have h3 : 0 < 3*r := by positivity
  have hp : Measurable (gaussianAverage (IsotropicGaussianHolder.matrix (3*r)) F) :=
    (IsotropicGaussianJets.smooth h3 F hF M hM 0).continuous.measurable
  have hi (z : State n) : Integrable (fun y => F (z+y))
      (multivariateGaussian 0 (IsotropicGaussianHolder.matrix (n := n) r)) :=
    Integrable.of_bound (hF.comp (measurable_const.add measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using hM _)
  have hj (z : State n) : Integrable
      (fun y => gaussianAverage (IsotropicGaussianHolder.matrix (3*r)) F (z+y))
      (multivariateGaussian 0 (IsotropicGaussianHolder.matrix (n := n) r)) :=
    Integrable.of_bound (hp.comp (measurable_const.add measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using average_bound _ F M hM _)
  funext z
  change _=∫ y, F (z+y)-gaussianAverage (IsotropicGaussianHolder.matrix (3*r)) F (z+y)
    ∂multivariateGaussian 0 (IsotropicGaussianHolder.matrix r)
  rw [integral_sub (hi z) (hj z)]
  change band r F z=gaussianAverage (IsotropicGaussianHolder.matrix r) F z-
    gaussianAverage (IsotropicGaussianHolder.matrix r) (gaussianAverage (IsotropicGaussianHolder.matrix (3*r)) F) z
  rw [gaussianAverage_composition _ _ (IsotropicGaussianHolder.nonnegative hr.le)
    (IsotropicGaussianHolder.nonnegative h3.le) F hF hM]
  have he : IsotropicGaussianHolder.matrix (n := n) r+IsotropicGaussianHolder.matrix (3*r)=
      IsotropicGaussianHolder.matrix (4*r) := by
    unfold IsotropicGaussianHolder.matrix
    rw [← add_smul]
    congr 1
    ring
  rw [he]
  rfl

/-- Quantitative all-order vector Bernstein estimate for the actual
Gaussian covariance band. No derivatives of the rough coefficient occur. -/
theorem jet_bound {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (k : ℕ) (z : State n) :
    ‖iteratedFDeriv ℝ k (band r F) z‖ ≤
      (K*(3*r)^(β/2)*GaussianNormMoment.moment (Fin n) β)*
        IsotropicGaussianJets.constant n k*((Real.sqrt r)⁻¹)^k := by
  have h3 : 0 < 3*r := by positivity
  rw [identity hr F hF M hM]
  apply IsotropicGaussianJets.bound hr _
    (hF.sub (IsotropicGaussianJets.smooth h3 F hF M hM 0).continuous.measurable)
  intro y
  rw [Pi.sub_apply,abs_sub_comm]
  exact displacement h3.le hK hβ F hF M hM hH y

def finiteConstant (n N : ℕ) : ℝ := ∑ j ∈ Finset.range (N+1), IsotropicGaussianJets.constant n j

theorem finiteConstant_nonneg (n N : ℕ) : 0 ≤ finiteConstant n N :=
  Finset.sum_nonneg (fun _ _ => IsotropicGaussianJets.constant_nonneg _ _)

theorem constant_le {N j : ℕ} (hj : j ≤ N) :
    IsotropicGaussianJets.constant n j ≤ finiteConstant n N := by
  change IsotropicGaussianJets.constant n j ≤ ∑ i ∈ Finset.range (N+1), IsotropicGaussianJets.constant n i
  exact Finset.single_le_sum (fun i _ => IsotropicGaussianJets.constant_nonneg n i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- One constant controls all derivative orders used by a fixed finite
comparison depth. This has exactly the amplitude/frequency form of the
existing full-vector clipped-root theorem. -/
theorem uniform_jets {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) (N j : ℕ) (hj : j ≤ N) (z : State n) :
    ‖iteratedFDeriv ℝ j (band r F) z‖ ≤
      ((K*(3*r)^(β/2)*GaussianNormMoment.moment (Fin n) β)*finiteConstant n N)*
        ((Real.sqrt r)⁻¹)^j := by
  have hAmp : 0 ≤ K*(3*r)^(β/2)*GaussianNormMoment.moment (Fin n) β :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) (GaussianNormMoment.nonneg _)
  exact (jet_bound hr hK hβ F hF M hM hH j z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (constant_le hj) hAmp)
      (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg r)) _))

theorem boundedSmooth {r K β : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M)
    (hH : ∀ z w, |F z-F w| ≤ K*‖z-w‖^β) :
    SmoothCylinders.BoundedSmooth (band r F) := by
  refine ⟨contDiff_infty.mpr (fun j => ?_),fun j => ⟨_,fun z => jet_bound hr hK hβ F hF M hM hH j z⟩⟩
  exact (IsotropicGaussianJets.smooth hr F hF M hM j).sub
    (IsotropicGaussianJets.smooth (by positivity : 0 < 4*r) F hF M hM j)

end SHEStochastic.IsotropicGaussianBands
