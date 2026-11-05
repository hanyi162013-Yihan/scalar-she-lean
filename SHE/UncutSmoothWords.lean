module

public import SHE.CutoffCarriers
public import SHE.NormalizedInsertion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.UncutSmoothWords
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore
open GaussianConvolution SmoothCylinders UniformSmooth NormalizedInsertion
open Classical
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual recursive insertion, with only the strict time ordering
and no positive time-gap cutoff. All original stops and targets are retained. -/
def test : (k : ℕ) → History P k → WordRecursion.State (n+k) → ℝ
  | 0 => L.test
  | k+1 => fun p => core R.totalVariance (R.reference ((carrier L k).nodeTime p,p.2.2))
      (row L k p) (gaussianAverage ((carrier L k).nodeCovariance p).val (test k p.1))

def weight : (k : ℕ) → History P k → ℝ
  | 0 => fun _ => 1
  | k+1 => fun p => weight k p.1 * ‖row L k p‖^2

/-- Unit Hilbert directions separate the genuine heat-history weight
from all smooth state derivatives. No lower bound on a row norm is needed. -/
def normalized : (k : ℕ) → History P k → WordRecursion.State (n+k) → ℝ
  | 0 => L.test
  | k+1 => fun p => core R.totalVariance (R.reference ((carrier L k).nodeTime p,p.2.2))
      (unitRow (row L k p)) (gaussianAverage ((carrier L k).nodeCovariance p).val (normalized k p.1))

theorem weight_nonneg (k : ℕ) (p : History P k) : 0 ≤ weight L k p := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (ih p.1) (sq_nonneg _)

theorem weight_measurable (k : ℕ) : Measurable (weight L k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (ih.comp measurable_fst).mul ((row_measurable L k).norm.pow_const 2)

theorem normalized_uniform (k : ℕ) : UniformBoundedSmooth (normalized L k) := by
  induction k with
  | zero => exact L.test_uniform
  | succ k ih =>
    have hG := (uniform_reindex ih Prod.fst).average
      (fun p : History P k × (ℝ × HeatCircle) =>
        multivariateGaussian (0 : WordRecursion.State (n+k)) ((carrier L k).nodeCovariance p).val)
      (fun _ => inferInstance)
    exact core_uniform R.totalVariance_smooth hG _ _ R.upper_nonneg
      (fun _ => R.reference_bound _) zero_le_one (fun _ => norm_unitRow_le _)

theorem normalized_measurable (k : ℕ) :
    Measurable (fun p : History P k × WordRecursion.State (n+k) => normalized L k p.1 p.2) := by
  induction k with
  | zero => exact L.test_measurable
  | succ k ih =>
    have hF : Measurable (fun p : (History P k × (ℝ × HeatCircle)) × WordRecursion.State (n+k) =>
        normalized L k p.1.1 p.2) := ih.comp (measurable_fst.fst.prodMk measurable_snd)
    have hG := MeasurableWords.gaussian_average_measurable (carrier L k).nodeCovariance_measurable
      hF (fun p => ((normalized_uniform L k).smooth p.1).continuous)
    exact core_measurable R.totalVariance_smooth.smooth.continuous.measurable
      (R.reference_measurable.comp ((carrier L k).nodeTime_measurable.prodMk measurable_snd.snd))
      (measurable_unitRow.comp (row_measurable L k)) hG
      (fun p => ((uniform_reindex (normalized_uniform L k) Prod.fst).average
        (fun p : History P k × (ℝ × HeatCircle) => multivariateGaussian
          (0 : WordRecursion.State (n+k)) ((carrier L k).nodeCovariance p).val)
        (fun _ => inferInstance)).smooth p |>.of_le (by simp))

theorem test_eq_weight_normalized (k : ℕ) (p : History P k) :
    test L k p = weight L k p • normalized L k p := by
  induction k with
  | zero => exact (one_smul ℝ (L.test p)).symm
  | succ k ih =>
    change core _ _ _ (gaussianAverage _ (test L k p.1))=_
    rw [ih p.1]
    change core _ _ _ (GaussianSmooth.average _ (_ • normalized L k p.1))=_
    rw [average_smul,core_weighted_unitRow]
    rfl

theorem test_measurable (k : ℕ) :
    Measurable (fun p : History P k × WordRecursion.State (n+k) => test L k p.1 p.2) := by
  have hh := ((weight_measurable L k).comp measurable_fst).smul (normalized_measurable L k)
  convert hh using 1
  funext p
  exact congrFun (test_eq_weight_normalized L k p.1) p.2

/-- The uncut finite-depth bound has a genuine heat-history weight;
the constant is independent of every positive time cutoff. -/
theorem test_norm_bound (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p z, ‖test L k p z‖ ≤ M * weight L k p := by
  obtain ⟨M,hMn,hM⟩ := (normalized_uniform L k).norm_bound
  refine ⟨M,hMn,fun p z => ?_⟩
  rw [test_eq_weight_normalized,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg L k p)]
  nlinarith [hM p z,weight_nonneg L k p]

end SHE.UncutSmoothWords
