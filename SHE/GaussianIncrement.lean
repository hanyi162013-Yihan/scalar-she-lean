module

public import SHE.GaussianSmooth

@[expose] public section
set_option autoImplicit false

/-! Actual finite Gaussian increments, including singular covariance.
The third moment is controlled by the physical covariance trace. -/
noncomputable section
namespace SHE.GaussianIncrement
open Set MeasureTheory ProbabilityTheory Matrix
open scoped MeasureTheory
abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem gaussian_convolution {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    multivariateGaussian (0 : State n) A ∗ multivariateGaussian 0 B = multivariateGaussian 0 (A + B) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hA, charFun_multivariateGaussian hB,
    charFun_multivariateGaussian (hA.add hB), ← Complex.exp_add]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    add_mulVec, dotProduct_add, Complex.ofReal_add]
  congr 1
  ring

theorem covariance_trace_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    0 ≤ A.trace := Finset.sum_nonneg (fun _ _ => hA.diag_nonneg)

theorem covariance_diag_le_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i : Fin n) : A i i ≤ A.trace := by
  exact Finset.single_le_sum (fun j _ => hA.diag_nonneg (i := j)) (Finset.mem_univ i)

theorem coordinate_mean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ x : State n, x i ∂multivariateGaussian 0 A) = 0 := by
  have he := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : State n) A))
  simpa only [id_eq, EuclideanSpace.coe_proj, integral_id_multivariateGaussian, map_zero] using he

theorem coordinate_product_moment {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i j : Fin n) :
    (∫ x : State n, x i * x j ∂multivariateGaussian 0 A) = A i j := by
  have hi := IsGaussian.memLp_dual (multivariateGaussian (0 : State n) A) (EuclideanSpace.proj i) 2 (by norm_num)
  have hj := IsGaussian.memLp_dual (multivariateGaussian (0 : State n) A) (EuclideanSpace.proj j) 2 (by norm_num)
  have he := covariance_eq_sub hi hj
  simp only [EuclideanSpace.coe_proj] at he
  rw [covariance_eval_multivariateGaussian hA] at he
  simpa only [Pi.mul_apply, coordinate_mean, zero_mul, sub_zero] using he.symm

theorem quadratic_moment {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (H : State n →L[ℝ] State n →L[ℝ] ℝ) :
    (∫ x : State n, H x x ∂multivariateGaussian 0 A) =
      ∑ i : Fin n, ∑ j : Fin n, A i j * H (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hi (i j : Fin n) : Integrable (fun x : State n => x i * x j) (multivariateGaussian 0 A) :=
    (IsGaussian.memLp_dual (multivariateGaussian (0 : State n) A) (EuclideanSpace.proj i) 2 (by norm_num)).integrable_mul
      (IsGaussian.memLp_dual (multivariateGaussian (0 : State n) A) (EuclideanSpace.proj j) 2 (by norm_num))
  simp_rw [WordRecursion.bilinear_mixed_pairs H]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, coordinate_product_moment hA]
    · intro j _
      exact (hi i j).mul_const _
  · intro i _
    exact integrable_finsetSum Finset.univ (fun j _ => (hi i j).mul_const _)

theorem coordinate_second_moment {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i : Fin n) :
    (∫ x : State n, x i ^ 2 ∂multivariateGaussian 0 A) = A i i := by
  have hp := measurePreserving_eval_multivariateGaussian (μ := (0 : State n)) hA (i := i)
  have hl : HasLaw (fun x : State n => x i) (gaussianReal 0 (A i i).toNNReal) (multivariateGaussian 0 A) :=
    ⟨hp.measurable.aemeasurable, by simpa using hp.map_eq⟩
  calc
    _ = ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 (A i i).toNNReal := by
      simpa only [Function.comp_def] using hl.integral_comp (f := fun z : ℝ => z ^ 2) (by fun_prop)
    _ = _ := by rw [GaussianAudit.gaussian_second_moment, Real.coe_toNNReal _ hA.diag_nonneg]

theorem coordinate_fourth_moment {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (i : Fin n) :
    (∫ x : State n, x i ^ 4 ∂multivariateGaussian 0 A) = 3 * (A i i) ^ 2 := by
  have hp := measurePreserving_eval_multivariateGaussian (μ := (0 : State n)) hA (i := i)
  have hl : HasLaw (fun x : State n => x i) (gaussianReal 0 (A i i).toNNReal) (multivariateGaussian 0 A) :=
    ⟨hp.measurable.aemeasurable, by simpa using hp.map_eq⟩
  calc
    _ = ∫ z : ℝ, z ^ 4 ∂gaussianReal 0 (A i i).toNNReal := by
      simpa only [Function.comp_def] using hl.integral_comp (f := fun z : ℝ => z ^ 4) (by fun_prop)
    _ = _ := by rw [GaussianAudit.gaussian_fourth_moment, Real.coe_toNNReal _ hA.diag_nonneg]

theorem norm_second_moment {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) :
    (∫ x : State n, ‖x‖ ^ 2 ∂multivariateGaussian 0 A) = A.trace := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp only [coordinate_second_moment hA, Matrix.trace, Matrix.diag]
  · intro i _
    exact (IsGaussian.memLp_dual (multivariateGaussian (0 : State n) A)
      (EuclideanSpace.proj i) 2 (by norm_num)).integrable_sq

theorem norm_fourth_moment_bound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) :
    (∫ x : State n, ‖x‖ ^ 4 ∂multivariateGaussian 0 A) ≤ 3 * n * A.trace ^ 2 := by
  have hi4 := (IsGaussian.memLp_id (multivariateGaussian (0 : State n) A) 4 (by norm_num)).integrable_norm_pow
    (p := 4) (by norm_num)
  simp only [id_eq] at hi4
  have hi (i : Fin n) : Integrable (fun x : State n => x i ^ 4) (multivariateGaussian 0 A) := by
    have hp := measurePreserving_eval_multivariateGaussian (μ := (0 : State n)) hA (i := i)
    exact (hp.integrable_comp (by fun_prop)).mpr (GaussianAudit.integrable_gaussian_power (A i i).toNNReal 4)
  calc
    _ ≤ ∫ x : State n, (n : ℝ) * ∑ i : Fin n, x i ^ 4 ∂multivariateGaussian 0 A := by
      apply integral_mono hi4 ((integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul n)
      intro x
      have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) (fun i => x i ^ 2)
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← EuclideanSpace.real_norm_sq_eq, ← pow_mul,
        show 2 * 2 = 4 by rfl] using he
    _ = (n : ℝ) * ∑ i : Fin n, 3 * (A i i) ^ 2 := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)]
      simp only [coordinate_fourth_moment hA]
    _ ≤ (n : ℝ) * (3 * A.trace ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hA.diag_nonneg (i := i))) (by norm_num)
    _ = _ := by ring

theorem norm_third_moment_bound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) :
    (∫ x : State n, ‖x‖ ^ 3 ∂multivariateGaussian 0 A) ≤
      Real.sqrt (3 * n) * A.trace * Real.sqrt A.trace := by
  let μ := multivariateGaussian (0 : State n) A
  have hi2 : MemLp (fun x : State n => ‖x‖) 2 μ :=
    (IsGaussian.memLp_id μ 2 (by norm_num)).norm
  have hi4 := (IsGaussian.memLp_id μ 4 (by norm_num)).integrable_norm_pow (p := 4) (by norm_num)
  simp only [id_eq] at hi4
  have hs2 : MemLp (fun x : State n => ‖x‖ ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (by
      simpa only [← pow_mul, show 2 * 2 = 4 by rfl] using hi4)
  have hh := ProfileL2.integral_mul_normTwo_bound hi2 hs2
  have hbound : ProfileL2.normTwo μ (fun x : State n => ‖x‖ ^ 2) ≤ Real.sqrt (3 * n) * A.trace := by
    have hs := ProfileL2.normTwo_sq μ (fun x : State n => ‖x‖ ^ 2)
    simp only [← pow_mul, show 2 * 2 = 4 by rfl] at hs
    have hb := norm_fourth_moment_bound hA
    change (∫ x : State n, ‖x‖ ^ 4 ∂μ) ≤ _ at hb
    have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * n by positivity)
    have ht := covariance_trace_nonneg hA
    apply (sq_le_sq₀ (ProfileL2.normTwo_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) ht)).mp
    rw [mul_pow, hr, hs]
    exact hb
  have he : ProfileL2.normTwo μ (fun x : State n => ‖x‖) = Real.sqrt A.trace := by
    unfold ProfileL2.normTwo
    rw [norm_second_moment hA]
  simp only [show (fun x : State n => ‖x‖ * ‖x‖ ^ 2) = (fun x => ‖x‖ ^ 3) by funext x; ring] at hh
  exact (le_abs_self _).trans (hh.trans ((mul_le_mul_of_nonneg_left hbound (ProfileL2.normTwo_nonneg _ _)).trans_eq (by rw [he]; ring)))

end SHE.GaussianIncrement
