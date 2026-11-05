module

public import SHE.GaussianFiniteSum
public import SHE.GaussianAssignmentSupport
public import SHE.GaussianReferenceLeafMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

/-! Assignment suppression changes the Gaussian law but never its physical
mean or its full reference baseline. These are the literal reduced laws. -/
namespace SHE.SuppressedGaussianLaw
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianAssignmentBlocks
open scoped BigOperators
variable {n r : ℕ}

def retained (is : List (Fin r)) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (j : Fin r) :=
  if j ∈ is then 0 else A j

def covariance (is : List (Fin r)) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) := (∑ j, retained is A j) + B

theorem suppress_apply (is : List (Fin r)) (x : Fin r → State n) (j : Fin r) :
    suppress is x j = if j ∈ is then 0 else x j := by
  induction is generalizing x with
  | nil => simp [suppress]
  | cons i is ih =>
    rw [suppress, ih]
    by_cases hj : j ∈ is
    · simp [hj]
    · by_cases hji : j = i
      · subst j; simp [hj]
      · simp [hj, hji, Function.update]

theorem retained_posSemidef (is : List (Fin r)) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).PosSemidef) (j : Fin r) : (retained is A j).PosSemidef := by
  unfold retained
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact hA j

theorem covariance_posSemidef (is : List (Fin r)) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).PosSemidef) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) :
    (covariance is A B).PosSemidef :=
  (Matrix.posSemidef_sum _ (fun j _ => retained_posSemidef is A hA j)).add hB

theorem map_suppress (is : List (Fin r)) (A : Fin r → Matrix (Fin n) (Fin n) ℝ) :
    (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).map (suppress is) =
      Measure.pi (fun j => multivariateGaussian (0 : State n) (retained is A j)) := by
  let f : Fin r → State n → State n := fun j x => if j ∈ is then 0 else x
  have hf : ∀ j, Measurable (f j) := by
    intro j
    dsimp [f]
    split_ifs <;> fun_prop
  have hm (j : Fin r) : (multivariateGaussian (0 : State n) (A j)).map (f j) =
      multivariateGaussian 0 (retained is A j) := by
    dsimp [f, retained]
    split_ifs
    · rw [Measure.map_const]
      simp [SHE.CovarianceMatrix.multivariateGaussian_zero_covariance]
    · exact Measure.map_id
  have he : suppress is = fun x j => f j (x j) := by
    funext x j
    exact suppress_apply is x j
  rw [he, Measure.pi_map_pi (fun j => (hf j).aemeasurable)]
  simp_rw [hm]

theorem map_suppressed_sum (is : List (Fin r)) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).PosSemidef) :
    (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).map
      (fun x => ∑ j, suppress is x j) =
      multivariateGaussian 0 (∑ j, retained is A j) := by
  have hs : Measurable (suppress is : (Fin r → State n) → _) := by
    apply Measurable.of_eval
    intro j
    simp_rw [suppress_apply]
    by_cases hj : j ∈ is <;> simp only [hj, ite_true, ite_false] <;> fun_prop
  calc
    _ = ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).map
        (suppress is)).map (fun x : Fin r → State n => ∑ j, x j) :=
      (Measure.map_map (by fun_prop) hs).symm
    _ = _ := by
      rw [map_suppress is A]
      exact GaussianFiniteSum.map_sum r (retained is A) (retained_posSemidef is A hA)

theorem map_suppressed_sum_residual (is : List (Fin r))
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) :
    ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)).map
      (fun x : (Fin r → State n) × State n => (∑ j, suppress is x.1 j) + x.2) =
      multivariateGaussian 0 (covariance is A B) := by
  let μ := Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))
  let ν := multivariateGaussian (0 : State n) B
  have hs : Measurable (fun x : Fin r → State n => ∑ j, suppress is x j) := by
    simp_rw [suppress_apply]
    fun_prop
  have hp : (μ.prod ν).map (fun x : (Fin r → State n) × State n =>
      (∑ j, suppress is x.1 j) + x.2) =
      (μ.map (fun x => ∑ j, suppress is x j)) ∗ ν := by
    unfold Measure.conv
    rw [show (μ.map (fun x => ∑ j, suppress is x j)).prod ν =
        (μ.map (fun x => ∑ j, suppress is x j)).prod (ν.map id) by rw [Measure.map_id],
      Measure.map_prod_map _ _ hs measurable_id,
      Measure.map_map (by fun_prop) (hs.prodMap measurable_id)]
    rfl
  rw [hp, map_suppressed_sum is A hA, multivariateGaussian_convolution _ _
    (Matrix.posSemidef_sum _ (fun j _ => retained_posSemidef is A hA j)) hB]
  rfl

theorem coordinate_domination (is : List (Fin r))
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    covariance is A B i i ≤ ((∑ j, A j) + B) i i := by
  simp only [covariance, Matrix.add_apply, Matrix.sum_apply]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j _
  dsimp [retained]
  split_ifs
  · exact (hA j).diag_nonneg
  · exact le_rfl

theorem coordinate_hasLaw (is : List (Fin r))
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) (i : Fin n) :
    HasLaw (fun x : (Fin r → State n) × State n => ((∑ j, suppress is x.1 j) + x.2) i)
      (gaussianReal 0 (covariance is A B i i).toNNReal)
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B)) := by
  have hh : HasLaw (fun x : (Fin r → State n) × State n => (∑ j, suppress is x.1 j) + x.2)
      (multivariateGaussian 0 (covariance is A B))
      ((Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
        (multivariateGaussian (0 : State n) B)) := by
    refine ⟨?_, map_suppressed_sum_residual is A hA B hB⟩
    simp_rw [suppress_apply]
    fun_prop
  have he := measurePreserving_eval_multivariateGaussian
    (μ := (0 : State n)) (covariance_posSemidef is A hA B hB) (i := i)
  have hl : HasLaw (fun y : State n => y i)
      (gaussianReal 0 (covariance is A B i i).toNNReal)
      (multivariateGaussian (0 : State n) (covariance is A B)) := by
    exact ⟨he.measurable.aemeasurable, by simpa using he.map_eq⟩
  exact hl.fun_comp hh

end SHE.SuppressedGaussianLaw
