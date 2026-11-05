module

public import SHE.GaussianConvolution
public import SHE.GaussianIncrement
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianFiniteSum
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
open scoped BigOperators
variable {n : ℕ}

/-- The sum of the actual independent full-vector Gaussian old fractions
has exactly the summed covariance, including every singular rank. -/
theorem map_sum (r : ℕ) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).PosSemidef) :
    (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).map
      (fun y : Fin r → State n => ∑ j, y j) =
      multivariateGaussian 0 (∑ j, A j) := by
  induction r with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [Measure.map_const]
    simp only [measure_univ, one_smul, SHE.CovarianceMatrix.multivariateGaussian_zero_covariance]
  | succ r ih =>
    let μ : Fin (r + 1) → Measure (State n) := fun j => multivariateGaussian 0 (A j)
    let ν : Measure (Fin r → State n) := Measure.pi (fun j => μ ((0 : Fin (r + 1)).succAbove j))
    let insert := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => State n) 0).symm
    have hm : ((μ 0).prod ν).map insert = Measure.pi μ :=
      ((measurePreserving_piFinSuccAbove μ 0).symm).map_eq
    have hsum : (fun y : State n × (Fin r → State n) => ∑ j, insert y j) =
        fun y => y.1 + ∑ j, y.2 j := by
      funext y
      change (∑ j, (Fin.insertNth 0 y.1 y.2 : Fin (r + 1) → State n) j) = _
      rw [Fin.sum_univ_succAbove _ 0]
      simp only [Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
    have hpush : ((μ 0).prod ν).map (fun y : State n × (Fin r → State n) => y.1 + ∑ j, y.2 j) =
        (μ 0) ∗ (ν.map (fun y => ∑ j, y j)) := by
      unfold Measure.conv
      rw [show (μ 0).prod (ν.map (fun y => ∑ j, y j)) =
        ((μ 0).map id).prod (ν.map (fun y => ∑ j, y j)) by rw [Measure.map_id],
        Measure.map_prod_map _ _ measurable_id (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [← hm, Measure.map_map (by fun_prop) insert.measurable]
    change ((μ 0).prod ν).map (fun y => ∑ j, insert y j) = _
    rw [hsum, hpush]
    have ht := ih (fun j => A ((0 : Fin (r + 1)).succAbove j)) (fun j => hA _)
    rw [show ν.map (fun y => ∑ j, y j) = multivariateGaussian 0
        (∑ j, A ((0 : Fin (r + 1)).succAbove j)) from ht]
    rw [multivariateGaussian_convolution (A 0) _ (hA 0)
      (Matrix.posSemidef_sum _ (fun j _ => hA _))]
    congr 1
    exact (Fin.sum_univ_succAbove _ 0).symm

end SHE.GaussianFiniteSum
