module

public import SHE.SignedTransport
public import SHE.CoarseCompression
public import SHE.StepInput
public import SHE.GenerationBound

@[expose] public section
set_option autoImplicit false

/-!
Actual signed Haar prefix and heat estimates, uniform in the fine dyadic
grid. The coefficient remains signed inside the massive negative Fourier
norm. The file also constructs fixed physical Haar columns for arbitrary
circle L² coefficients and proves their local-mass continuity and exact
finite-grid refinement identities. The countable HS limit theorem states
the remaining convergence/identification inputs explicitly; it does not
postulate an infinite transport estimate.
-/

noncomputable section
namespace SHE.FiniteHaar
open Finset Matrix FiniteTransport MeasureTheory AddCircle CircleHeat
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The actual signed coarse-output bound is uniform in every finer grid.
All prefix and Christoffel hypotheses of the general compression theorem
are proved for the explicitly constructed weighted Haar factors. -/
theorem signed_prefix_frobenius (n k : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k},
      ∑ j : Option (DetailIndex n),
        (referenceFactor n c i.val j - referenceFactor n d i.val j) ^ 2) ≤
      U / m ^ 2 * ((((2 ^ k : ℕ) : ℝ)) / (((2 ^ n : ℕ) : ℝ))) *
        ∑ x, (c x - d x) ^ 2 := by
  have hcp : ∀ x, 0 < c x := fun x => hm.trans_le (hc x).1
  have hdp : ∀ x, 0 < d x := fun x => hm.trans_le (hd x).1
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  exact CoarseCompression.signed_principal_frobenius
    (fun i : Option (DetailIndex n) => modeLevel n i ≤ k)
    (haarMatrix n (fun _ => 1)) (referenceHaar_orthogonal n)
    (referenceFactor n c) (referenceFactor n d) c d m U _ hm hU
    (referenceFactor_lower n c hcp) (referenceFactor_lower n d hdp)
    (referenceFactor_diag_pos n c hcp) (referenceFactor_diag_pos n d hdp)
    (referenceFactor_covariance n c hcp) (referenceFactor_covariance n d hdp) hc hd
    (referenceFactor_prefix_zero n k c hcp) (referenceFactor_prefix_zero n k d hdp)
    (referenceHaar_prefix_row_bound n k)

/-- The physical coefficient difference on the literal periodic dyadic grid. -/
def coefficientDifference (n : ℕ) (c d : Grid n → ℝ) : AddCircle (1 : ℝ) → ℂ :=
  CircleStep.circleStep (2 ^ n) (fun j =>
    c ((gridCellEquiv n).symm j) - d ((gridCellEquiv n).symm j))

theorem coefficientDifference_L2 (n : ℕ) (c d : Grid n → ℝ) :
    (∫ x : AddCircle (1 : ℝ), ‖coefficientDifference n c d x‖ ^ 2 ∂haarAddCircle) =
      (((2 ^ n : ℕ) : ℝ))⁻¹ * ∑ x, (c x - d x) ^ 2 := by
  rw [coefficientDifference, CircleStep.circleStep_L2]
  unfold CyclicStep.stepL2Sq FiniteTransport.vectorSq
  congr 1
  exact Equiv.sum_comp (gridCellEquiv n).symm (fun x => (c x - d x) ^ 2)

/-- The central physical-space prefix estimate of signed Haar transport:
`2^k`, rather than the fine leaf count, controls every coarse-output prefix. -/
theorem signed_prefix_physical (n k : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k},
      ∑ j : Option (DetailIndex n),
        (referenceFactor n c i.val j - referenceFactor n d i.val j) ^ 2) ≤
      U / m ^ 2 * (((2 ^ k : ℕ) : ℝ)) *
        (∫ x : AddCircle (1 : ℝ), ‖coefficientDifference n c d x‖ ^ 2 ∂haarAddCircle) := by
  have h := signed_prefix_frobenius n k c d m U hm hc hd
  rw [coefficientDifference_L2]
  apply h.trans_eq
  ring

def signedGenerationColumn (n k : ℕ) (c d : Grid n → ℝ) (j : Option (DetailIndex n)) : CircleL2 :=
  generationSynthesis n k (fun i => referenceFactor n c i j - referenceFactor n d i j)

theorem signed_generation_energy (n k : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖signedGenerationColumn n k c d j‖ ^ 2) ≤
      U / m ^ 2 * (((2 ^ (k + 1) : ℕ) : ℝ)) *
        (∫ x : AddCircle (1 : ℝ), ‖coefficientDifference n c d x‖ ^ 2 ∂haarAddCircle) := by
  let e : Option (DetailIndex n) → ℝ := fun i =>
    ∑ j : Option (DetailIndex n), (referenceFactor n c i j - referenceFactor n d i j) ^ 2
  have he : ∀ i, 0 ≤ e i := fun i => sum_nonneg (fun j _ => sq_nonneg _)
  have hsum : (∑ j : Option (DetailIndex n), ‖signedGenerationColumn n k c d j‖ ^ 2) =
      ∑ i : Option (DetailIndex n), if modeLevel n i = k + 1 then e i else 0 := by
    simp only [signedGenerationColumn, generationSynthesis_norm_sq]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    by_cases hlevel : modeLevel n i = k + 1 <;>
      simp only [hlevel, ↓reduceIte, sum_const_zero, e]
  have hpref : (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k + 1}, e i.val) =
      ∑ i : Option (DetailIndex n), if modeLevel n i ≤ k + 1 then e i else 0 := by
    rw [← Finset.sum_subtype (univ.filter (fun i => modeLevel n i ≤ k + 1))
      (by simp) e, Finset.sum_filter]
  have hle : (∑ i : Option (DetailIndex n), if modeLevel n i = k + 1 then e i else 0) ≤
      ∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k + 1}, e i.val := by
    rw [hpref]
    apply sum_le_sum
    intro i hi
    by_cases hlevel : modeLevel n i = k + 1
    · rw [ite_eq_left hlevel, ite_eq_left (by omega)]
    · rw [ite_eq_right hlevel]
      split_ifs
      · exact he i
      · exact le_rfl
  rw [hsum]
  exact hle.trans (signed_prefix_physical n (k + 1) c d m U hm hc hd)

/-- The signed heat generation estimate for actual physical weighted-Haar
factor columns, uniform in all finer resolutions. -/
theorem signed_massive_heat_generation {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n k : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), weightedFourierSq (massiveWeight κ Λ ρ)
      (heat t (signedGenerationColumn n k c d j))) ≤
      inverseConstant κ ρ * (Λ + ((2 * 2 ^ k : ℕ) : ℝ) ^ 2) ^ ρ *
        min 1 (((2 * 2 ^ k : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) *
          (U / m ^ 2 * (((2 ^ (k + 1) : ℕ) : ℝ)) *
            (∫ x : AddCircle (1 : ℝ), ‖coefficientDifference n c d x‖ ^ 2 ∂haarAddCircle)) := by
  calc
    _ ≤ ∑ j : Option (DetailIndex n),
        inverseConstant κ ρ * (Λ + ((2 * 2 ^ k : ℕ) : ℝ) ^ 2) ^ ρ *
          min 1 (((2 * 2 ^ k : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) *
            ‖signedGenerationColumn n k c d j‖ ^ 2 :=
      sum_le_sum (fun j _ => massive_heat_generationSynthesis ht hκ hΛ hρ hρhalf n k _)
    _ = _ * (∑ j : Option (DetailIndex n), ‖signedGenerationColumn n k c d j‖ ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (signed_generation_energy n k c d m U hm hc hd)
      (mul_nonneg (mul_nonneg (inverseConstant_nonneg hκ hρ hρhalf) (by positivity))
        (le_min (by norm_num) (by positivity)))

/-- The actual coarse weighted-Haar factor rows are unchanged by replacing
the coefficient with its dyadic conditional averages. -/
theorem referenceFactor_prefix_coarseAverage (n k : ℕ) (c : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m) (hc : ∀ x, m ≤ c x ∧ c x ≤ U)
    (i : {i : Option (DetailIndex n) // modeLevel n i ≤ k}) (j : Option (DetailIndex n)) :
    referenceFactor n c i.val j = referenceFactor n (coarseAverage n k c) i.val j := by
  let p : Option (DetailIndex n) → Prop := fun i => modeLevel n i ≤ k
  let a := coarseAverage n k c
  have ha := coarseAverage_bounds n k c m U hc
  have hcp : ∀ x, 0 < c x := fun x => hm.trans_le (hc x).1
  have hap : ∀ x, 0 < a x := fun x => hm.trans_le (ha x).1
  have hcov : CoarseCompression.principal p (referenceFactor n c) *
      (CoarseCompression.principal p (referenceFactor n c))ᵀ =
      CoarseCompression.principal p (referenceFactor n a) *
        (CoarseCompression.principal p (referenceFactor n a))ᵀ := by
    rw [CoarseCompression.principal_covariance p _ (referenceFactor_prefix_zero n k c hcp),
      CoarseCompression.principal_covariance p _ (referenceFactor_prefix_zero n k a hap)]
    ext i j
    change (referenceFactor n c * (referenceFactor n c)ᵀ) i.val j.val =
      (referenceFactor n a * (referenceFactor n a)ᵀ) i.val j.val
    rw [referenceFactor_covariance n c hcp, referenceFactor_covariance n a hap,
      ordinaryCovarianceEntry_matrix, ordinaryCovarianceEntry_matrix]
    exact ordinaryCovarianceEntry_coarseAverage n k c i.val j.val i.property j.property
  have heq := CoarseCompression.triangular_covariance_unique
    (CoarseCompression.principal p (referenceFactor n c))
    (CoarseCompression.principal p (referenceFactor n a))
    (fun i j hij => referenceFactor_lower n c hcp hij)
    (fun i j hij => referenceFactor_lower n a hap hij)
    (fun i => referenceFactor_diag_pos n c hcp i.val)
    (fun i => referenceFactor_diag_pos n a hap i.val) hcov
  by_cases hj : modeLevel n j ≤ k
  · exact congrFun (congrFun heq i) ⟨j, hj⟩
  · rw [referenceFactor_prefix_zero n k c hcp i j hj,
      referenceFactor_prefix_zero n k a hap i j hj]

/-- The sharp prefix bound depends on the actual coarse conditional average
of the signed coefficient, rather than its full fine-grid `L²` size. -/
theorem signed_prefix_physical_averaged (n k : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k},
      ∑ j : Option (DetailIndex n),
        (referenceFactor n c i.val j - referenceFactor n d i.val j) ^ 2) ≤
      U / m ^ 2 * (((2 ^ k : ℕ) : ℝ)) *
        (∫ x : AddCircle (1 : ℝ),
          ‖coefficientDifference n (coarseAverage n k c) (coarseAverage n k d) x‖ ^ 2 ∂haarAddCircle) := by
  have hrow (i : {i : Option (DetailIndex n) // modeLevel n i ≤ k}) (j : Option (DetailIndex n)) :=
    referenceFactor_prefix_coarseAverage n k c m U hm hc i j
  simp_rw [hrow, referenceFactor_prefix_coarseAverage n k d m U hm hd]
  exact signed_prefix_physical n k (coarseAverage n k c) (coarseAverage n k d) m U hm
    (coarseAverage_bounds n k c m U hc) (coarseAverage_bounds n k d m U hd)

/-- Exact negative-input bound for the actual conditional average. It uses
the literal coarse step witness, the positive inverse inequality, and the
proved averaging energy identity in weighted Fourier duality. -/
theorem coarseAverage_negative (n k : ℕ) (hk : k ≤ n) (f : Grid n → ℝ)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    ‖gridStep n (coarseAverage n k f)‖ ^ 2 ≤
      inverseConstant κ ρ * (Λ + (((2 ^ k : ℕ) : ℝ)) ^ 2) ^ ρ *
        StepInput.negativeEnergy κ Λ ρ (gridStep n f) := by
  obtain ⟨v, hv⟩ := gridStep_coarseAverage_witness n k hk f
  let C := inverseConstant κ ρ * (Λ + (((2 ^ k : ℕ) : ℝ)) ^ 2) ^ ρ
  have hC : 0 ≤ C := mul_nonneg (inverseConstant_nonneg hκ hρ hρhalf) (by positivity)
  have hw (z : ℤ) : 0 < massiveWeight κ Λ ρ z :=
    Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg hΛ (sq_nonneg _)) _
  have hh := InputProjection.single_vector_bound (fourierBasis (T := (1 : ℝ)))
    (massiveWeight κ Λ ρ) hw (gridStep n f) (gridStep n (coarseAverage n k f)) C hC
  have hneg : StepInput.negativeEnergy κ Λ ρ (gridStep n f) =
      InputProjection.weightedEnergy (fourierBasis (T := (1 : ℝ)))
        (fun z => (massiveWeight κ Λ ρ z)⁻¹) (gridStep n f) := by
    simp only [StepInput.negativeEnergy, InputProjection.weightedEnergy, weightedFourierSq, fourierBasis_repr]
  rw [hneg]
  apply hh
  · simpa only [fourierBasis_repr] using StepInput.negativeEnergy_summable hΛ hρ.le (gridStep n f)
  · rw [hv]
    simpa only [fourierBasis_repr] using summable_stepLp_massive (2 ^ k) v hκ hΛ.le hρ hρhalf
  · exact gridStep_coarseAverage_pairing n k f
  · rw [hv]
    simpa only [InputProjection.weightedEnergy, weightedFourierSq, fourierBasis_repr, C] using
      stepLp_massive_inverse (2 ^ k) v hκ hΛ.le hρ hρhalf

/-- The actual signed coarse-output prefix estimate with the manuscript's
massive negative Fourier norm on the signed coefficient input. -/
theorem signed_prefix_negative (n k : ℕ) (hk : k ≤ n) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k},
      ∑ j : Option (DetailIndex n),
        (referenceFactor n c i.val j - referenceFactor n d i.val j) ^ 2) ≤
      U / m ^ 2 * (((2 ^ k : ℕ) : ℝ)) *
        (inverseConstant κ ρ * (Λ + (((2 ^ k : ℕ) : ℝ)) ^ 2) ^ ρ *
          StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))) := by
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have h := signed_prefix_physical_averaged n k c d m U hm hc hd
  have heq : (∫ x : AddCircle (1 : ℝ),
      ‖coefficientDifference n (coarseAverage n k c) (coarseAverage n k d) x‖ ^ 2 ∂haarAddCircle) =
      ‖gridStep n (coarseAverage n k (c - d))‖ ^ 2 := by
    rw [coefficientDifference_L2, gridStep_norm_sq, coarseAverage_sub]
    rfl
  rw [heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (coarseAverage_negative n k hk (c - d) hκ hΛ hρ hρhalf)
    (mul_nonneg (div_nonneg hU (sq_nonneg m)) (by positivity)))

theorem generation_energy_le_prefix (n k : ℕ)
    (x : Matrix (Option (DetailIndex n)) (Option (DetailIndex n)) ℝ) :
    (∑ j : Option (DetailIndex n), ‖generationSynthesis n k (fun i => x i j)‖ ^ 2) ≤
      ∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k + 1}, ∑ j, (x i.val j) ^ 2 := by
  let e : Option (DetailIndex n) → ℝ := fun i => ∑ j, (x i j) ^ 2
  have he : ∀ i, 0 ≤ e i := fun i => sum_nonneg (fun j _ => sq_nonneg _)
  have hsum : (∑ j : Option (DetailIndex n), ‖generationSynthesis n k (fun i => x i j)‖ ^ 2) =
      ∑ i : Option (DetailIndex n), if modeLevel n i = k + 1 then e i else 0 := by
    simp only [generationSynthesis_norm_sq]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    by_cases hlevel : modeLevel n i = k + 1 <;>
      simp only [hlevel, ↓reduceIte, sum_const_zero, e]
  rw [hsum]
  have hpref : (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k + 1}, e i.val) =
      ∑ i : Option (DetailIndex n), if modeLevel n i ≤ k + 1 then e i else 0 := by
    rw [← Finset.sum_subtype (univ.filter (fun i => modeLevel n i ≤ k + 1))
      (by simp) e, Finset.sum_filter]
  change _ ≤ ∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k + 1}, e i.val
  rw [hpref]
  apply sum_le_sum
  intro i hi
  by_cases hlevel : modeLevel n i = k + 1
  · rw [ite_eq_left hlevel, ite_eq_left (by omega)]
  · rw [ite_eq_right hlevel]
    split_ifs
    · exact he i
    · exact le_rfl

theorem heat_generationSynthesis_sq {t : ℝ} (ht : 0 < t) (n k : ℕ)
    (x : Option (DetailIndex n) → ℝ) :
    ‖heat t (generationSynthesis n k x)‖ ^ 2 ≤
      min 1 ((((2 ^ (k + 1) : ℕ) : ℝ))⁻¹ ^ 2 / (4 * t)) * ‖generationSynthesis n k x‖ ^ 2 := by
  have hmem := generationSynthesis_mem n k x
  have heq : detailProjection (2 ^ k) (generationSynthesis n k x) = generationSynthesis n k x :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  have hh := heat_detailProjection_sq ht (2 ^ k) (generationSynthesis n k x)
  rw [heq] at hh
  have hD : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; omega
  simpa only [hD] using hh

/-- The manuscript's signed heat generation estimate, with unweighted
heated output and the genuine massive negative norm on the signed input. -/
theorem signed_heat_generation_negative {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n k : ℕ) (hk : k + 1 ≤ n) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖heat t (signedGenerationColumn n k c d j)‖ ^ 2) ≤
      (U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))) *
        (((2 ^ (k + 1) : ℕ) : ℝ)) * (Λ + (((2 ^ (k + 1) : ℕ) : ℝ)) ^ 2) ^ ρ *
          min 1 ((((2 ^ (k + 1) : ℕ) : ℝ))⁻¹ ^ 2 / (4 * t)) := by
  have hprefix := signed_prefix_negative n (k + 1) hk c d m U hm hc hd hκ hΛ hρ hρhalf
  have hgen := generation_energy_le_prefix n k (referenceFactor n c - referenceFactor n d)
  have hgen' : (∑ j : Option (DetailIndex n), ‖signedGenerationColumn n k c d j‖ ^ 2) ≤
      U / m ^ 2 * (((2 ^ (k + 1) : ℕ) : ℝ)) *
        (inverseConstant κ ρ * (Λ + (((2 ^ (k + 1) : ℕ) : ℝ)) ^ 2) ^ ρ *
          StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))) := by
    apply hgen.trans
    exact hprefix
  calc
    _ ≤ ∑ j : Option (DetailIndex n),
        min 1 ((((2 ^ (k + 1) : ℕ) : ℝ))⁻¹ ^ 2 / (4 * t)) *
          ‖signedGenerationColumn n k c d j‖ ^ 2 :=
      sum_le_sum (fun j _ => heat_generationSynthesis_sq ht n k _)
    _ = _ * (∑ j : Option (DetailIndex n), ‖signedGenerationColumn n k c d j‖ ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ * (U / m ^ 2 * (((2 ^ (k + 1) : ℕ) : ℝ)) *
        (inverseConstant κ ρ * (Λ + (((2 ^ (k + 1) : ℕ) : ℝ)) ^ 2) ^ ρ *
          StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d)))) :=
      mul_le_mul_of_nonneg_left hgen' (le_min (by norm_num) (by positivity))
    _ = _ := by ring

theorem generationSynthesis_zero (n k : ℕ) (hk : n ≤ k) (x : Option (DetailIndex n) → ℝ) :
    generationSynthesis n k x = 0 := by
  have hzero : generationCoordinates n k x = 0 := by
    funext i
    have hlevel : modeLevel n i ≤ n := by
      cases i with
      | none => exact Nat.zero_le _
      | some i => exact detailLevel_le n i
    exact ite_eq_right (by omega)
  rw [generationSynthesis, hzero]
  exact map_zero (referenceSynthesisLinear n)

theorem negativeEnergy_nonneg (κ ρ : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (f : CircleL2) :
    0 ≤ StepInput.negativeEnergy κ Λ ρ f := by
  unfold StepInput.negativeEnergy weightedFourierSq
  apply tsum_nonneg
  intro z
  exact mul_nonneg (inv_nonneg.mpr (massiveWeight_nonneg hΛ κ ρ z)) (sq_nonneg _)

/-- The generation estimate is valid for every generation: generations
beyond the finite grid vanish as actual circle `L²` vectors. -/
theorem signed_heat_generation_negative_all {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n k : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖heat t (signedGenerationColumn n k c d j)‖ ^ 2) ≤
      (U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))) *
        (((2 ^ (k + 1) : ℕ) : ℝ)) * (Λ + (((2 ^ (k + 1) : ℕ) : ℝ)) ^ 2) ^ ρ *
          min 1 ((((2 ^ (k + 1) : ℕ) : ℝ))⁻¹ ^ 2 / (4 * t)) := by
  by_cases hk : k + 1 ≤ n
  · exact signed_heat_generation_negative ht hκ hΛ hρ hρhalf n k hk c d m U hm hc hd
  · have hk' : n ≤ k := by omega
    have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
    simp only [signedGenerationColumn, generationSynthesis_zero n k hk', map_zero, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (div_nonneg hU (sq_nonneg m))
        (inverseConstant_nonneg hκ hρ hρhalf)) (negativeEnergy_nonneg κ ρ hΛ.le _)) (by positivity))
      (by positivity)) (le_min (by norm_num) (by positivity))

def levelCoordinates (n r : ℕ) (x : Option (DetailIndex n) → ℝ) : Option (DetailIndex n) → ℝ :=
  fun i => if modeLevel n i = r then x i else 0

def levelSynthesis (n r : ℕ) (x : Option (DetailIndex n) → ℝ) : CircleL2 :=
  referenceSynthesis n (levelCoordinates n r x)

theorem levelSynthesis_norm_sq (n r : ℕ) (x : Option (DetailIndex n) → ℝ) :
    ‖levelSynthesis n r x‖ ^ 2 =
      ∑ i : Option (DetailIndex n), if modeLevel n i = r then (x i) ^ 2 else 0 := by
  rw [levelSynthesis, referenceSynthesis_norm_sq]
  unfold FiniteTransport.vectorSq levelCoordinates
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem referenceSynthesis_levels (n : ℕ) (x : Option (DetailIndex n) → ℝ) :
    referenceSynthesis n x = ∑ r ∈ range (n + 1), levelSynthesis n r x := by
  have hcoords : (∑ r ∈ range (n + 1), levelCoordinates n r x) = x := by
    funext i
    rw [Finset.sum_apply]
    have hlevel : modeLevel n i ≤ n := by
      cases i with
      | none => exact Nat.zero_le _
      | some i => exact detailLevel_le n i
    calc
      _ = levelCoordinates n (modeLevel n i) x i := by
        apply sum_eq_single (modeLevel n i)
        · intro r hr hri
          exact ite_eq_right (Ne.symm hri)
        · intro hnot
          exact (hnot (mem_range.mpr (by omega))).elim
      _ = x i := by simp [levelCoordinates]
  have hh := map_sum (referenceSynthesisLinear n) (fun r => levelCoordinates n r x) (range (n + 1))
  change referenceSynthesis n (∑ r ∈ range (n + 1), levelCoordinates n r x) =
    ∑ r ∈ range (n + 1), levelSynthesis n r x at hh
  rw [hcoords] at hh
  exact hh

theorem level_energy_le_prefix (n r : ℕ)
    (x : Matrix (Option (DetailIndex n)) (Option (DetailIndex n)) ℝ) :
    (∑ j : Option (DetailIndex n), ‖levelSynthesis n r (fun i => x i j)‖ ^ 2) ≤
      ∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ r}, ∑ j, (x i.val j) ^ 2 := by
  let e : Option (DetailIndex n) → ℝ := fun i => ∑ j, (x i j) ^ 2
  have he : ∀ i, 0 ≤ e i := fun i => sum_nonneg (fun j _ => sq_nonneg _)
  have hsum : (∑ j : Option (DetailIndex n), ‖levelSynthesis n r (fun i => x i j)‖ ^ 2) =
      ∑ i : Option (DetailIndex n), if modeLevel n i = r then e i else 0 := by
    simp only [levelSynthesis_norm_sq]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    by_cases hlevel : modeLevel n i = r <;>
      simp only [hlevel, ↓reduceIte, sum_const_zero, e]
  rw [hsum]
  have hpref : (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ r}, e i.val) =
      ∑ i : Option (DetailIndex n), if modeLevel n i ≤ r then e i else 0 := by
    rw [← Finset.sum_subtype (univ.filter (fun i => modeLevel n i ≤ r)) (by simp) e, Finset.sum_filter]
  change _ ≤ ∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ r}, e i.val
  rw [hpref]
  apply sum_le_sum
  intro i hi
  by_cases hlevel : modeLevel n i = r
  · rw [ite_eq_left hlevel, ite_eq_left (by omega)]
  · rw [ite_eq_right hlevel]
    split_ifs
    · exact he i
    · exact le_rfl

abbrev ColumnSpace (n : ℕ) := PiLp 2 (fun _ : Option (DetailIndex n) => CircleL2)

def heatedLevelColumns (n r : ℕ) (c d : Grid n → ℝ) (t : ℝ) : ColumnSpace n :=
  WithLp.toLp 2 (fun j => heat t (levelSynthesis n r
    (fun i => referenceFactor n c i j - referenceFactor n d i j)))

def heatedSignedColumns (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) : ColumnSpace n :=
  WithLp.toLp 2 (fun j => heat t (signedColumn n c d j))

theorem heatedLevelColumns_norm_sq (n r : ℕ) (c d : Grid n → ℝ) (t : ℝ) :
    ‖heatedLevelColumns n r c d t‖ ^ 2 =
      ∑ j : Option (DetailIndex n), ‖heat t (levelSynthesis n r
        (fun i => referenceFactor n c i j - referenceFactor n d i j))‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _ _

theorem heatedSignedColumns_norm_sq (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) :
    ‖heatedSignedColumns n c d t‖ ^ 2 =
      ∑ j : Option (DetailIndex n), ‖heat t (signedColumn n c d j)‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _ _

theorem heatedSignedColumns_levels (n : ℕ) (c d : Grid n → ℝ) (t : ℝ) :
    heatedSignedColumns n c d t = ∑ r ∈ range (n + 1), heatedLevelColumns n r c d t := by
  apply PiLp.ext
  intro j
  change heat t (signedColumn n c d j) = _
  rw [signedColumn, referenceSynthesis_levels, map_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, heatedLevelColumns]

theorem heatedLevelColumns_bound {t κ Λ ρ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n r : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    ‖heatedLevelColumns n r c d t‖ ≤
      Real.sqrt (U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))) *
        DyadicTransport.massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ r := by
  let C := U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (div_nonneg hU (sq_nonneg m)) (inverseConstant_nonneg hκ hρ hρhalf))
    (negativeEnergy_nonneg κ ρ hΛ.le _)
  rw [← Real.sqrt_sq (norm_nonneg (heatedLevelColumns n r c d t))]
  cases r with
  | zero =>
    apply constant_generation_sqrt_bound (sq_nonneg _) hC ht ht1 hΛ.le hρ.le
    rw [heatedLevelColumns_norm_sq]
    have hprefix := signed_prefix_negative n 0 (Nat.zero_le _) c d m U hm hc hd hκ hΛ hρ hρhalf
    have hgen := level_energy_le_prefix n 0 (referenceFactor n c - referenceFactor n d)
    calc
      _ ≤ ∑ j : Option (DetailIndex n), ‖levelSynthesis n 0
          (fun i => referenceFactor n c i j - referenceFactor n d i j)‖ ^ 2 := by
        apply sum_le_sum
        intro j hj
        exact pow_le_pow_left₀ (norm_nonneg _) (heat_contraction t _) 2
      _ ≤ _ := hgen.trans (hprefix.trans_eq (by simp only [pow_zero, Nat.cast_one, one_pow, mul_one, C]; ring))
  | succ k =>
    apply generation_sqrt_bound (k + 1) (sq_nonneg _) hC ht hΛ.le hρ.le
    rw [heatedLevelColumns_norm_sq]
    have hh := signed_heat_generation_negative_all ht hκ hΛ hρ hρhalf n k c d m U hm hc hd
    have hlevel (x : Option (DetailIndex n) → ℝ) : levelSynthesis n (k + 1) x = generationSynthesis n k x := rfl
    simp_rw [hlevel]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, signedGenerationColumn, C] using hh

/-- The full signed heat Hilbert--Schmidt estimate on every finite dyadic
grid, in the actual circle `L²` output and with the signed massive negative
Fourier norm on the coefficient input. The constant is uniform in `n`. -/
theorem signed_heat_finite_HS {t κ Λ ρ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    ‖heatedSignedColumns n c d t‖ ≤
      Real.sqrt (U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))) *
        DyadicTransport.signedHeatConstant ρ *
          (Λ ^ (ρ / 2) * t ^ (-(1 / 4 : ℝ)) + t ^ (-(1 / 4 : ℝ) - ρ / 2)) := by
  let C := Real.sqrt (U / m ^ 2 * inverseConstant κ ρ *
    StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d)))
  have hs := DyadicTransport.signed_heat_series ht ht1 hΛ.le hρ hρhalf
  rw [heatedSignedColumns_levels]
  calc
    _ ≤ ∑ r ∈ range (n + 1), ‖heatedLevelColumns n r c d t‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ range (n + 1), C * DyadicTransport.massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ r :=
      sum_le_sum (fun r _ => heatedLevelColumns_bound ht ht1 hκ hΛ hρ hρhalf n r c d m U hm hc hd)
    _ = C * ∑ r ∈ range (n + 1), DyadicTransport.massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ r :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑' r, DyadicTransport.massiveTerm (t ^ (-(1 / 2 : ℝ))) Λ ρ r := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact hs.1.sum_le_tsum _ (fun r _ => by unfold DyadicTransport.massiveTerm; positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hs.2 (Real.sqrt_nonneg
        (U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))))
      simpa only [C, mul_assoc] using hh

def signedHeatSqConstant (κ ρ m U : ℝ) : ℝ :=
  2 * (U / m ^ 2 * inverseConstant κ ρ) * (DyadicTransport.signedHeatConstant ρ) ^ 2

/-- The actual squared Hilbert--Schmidt estimate in the exact time powers
used by the damped-energy argument. -/
theorem signed_heat_finite_HS_sq {t κ Λ ρ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖heat t (signedColumn n c d j)‖ ^ 2) ≤
      signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d)) *
        (Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)) := by
  let C := U / m ^ 2 * inverseConstant κ ρ * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d))
  let D := DyadicTransport.signedHeatConstant ρ
  let A := Λ ^ (ρ / 2) * t ^ (-(1 / 4 : ℝ))
  let B := t ^ (-(1 / 4 : ℝ) - ρ / 2)
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (div_nonneg hU (sq_nonneg m)) (inverseConstant_nonneg hκ hρ hρhalf))
    (negativeEnergy_nonneg κ ρ hΛ.le _)
  have hh := signed_heat_finite_HS ht ht1 hκ hΛ hρ hρhalf n c d m U hm hc hd
  have hsq := pow_le_pow_left₀ (norm_nonneg (heatedSignedColumns n c d t)) hh 2
  change ‖heatedSignedColumns n c d t‖ ^ 2 ≤ (Real.sqrt C * D * (A + B)) ^ 2 at hsq
  rw [mul_pow, mul_pow, Real.sq_sqrt hC, heatedSignedColumns_norm_sq] at hsq
  have hA : A ^ 2 = Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) := by
    dsimp only [A]
    rw [mul_pow, ← Real.rpow_mul_natCast hΛ.le, ← Real.rpow_mul_natCast ht.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ρ / 2 * 2 = ρ by ring]
  have hB : B ^ 2 = t ^ (-(1 / 2 : ℝ) - ρ) := by
    dsimp only [B]
    rw [← Real.rpow_mul_natCast ht.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-(1 / 4 : ℝ) - ρ / 2) * 2 = -(1 / 2 : ℝ) - ρ by ring]
  calc
    _ ≤ C * D ^ 2 * (A + B) ^ 2 := hsq
    _ ≤ C * D ^ 2 * (2 * (A ^ 2 + B ^ 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (A - B)]) (mul_nonneg hC (sq_nonneg D))
    _ = _ := by rw [hA, hB]; dsimp only [C, D, signedHeatSqConstant]; ring

theorem heat_sq_le_at_one {t : ℝ} (ht : 1 ≤ t) (f : CircleL2) :
    ‖heat t f‖ ^ 2 ≤ ‖heat 1 f‖ ^ 2 := by
  have heq : t = (t - 1) + 1 := by ring
  rw [heq, heat_semigroup (by linarith : 0 ≤ t - 1) (by norm_num : (0 : ℝ) ≤ 1),
    ContinuousLinearMap.comp_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (heat_contraction (t - 1) (heat 1 f)) 2

/-- The large-time tail uses the same actual heat semigroup, by contraction
after age one. -/
theorem signed_heat_finite_HS_tail {t κ Λ ρ : ℝ} (ht : 1 ≤ t)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n : ℕ) (c d : Grid n → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖heat t (signedColumn n c d j)‖ ^ 2) ≤
      signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ (gridStep n (c - d)) * (Λ ^ ρ + 1) := by
  have hh := signed_heat_finite_HS_sq (by norm_num : (0 : ℝ) < 1) le_rfl
    hκ hΛ hρ hρhalf n c d m U hm hc hd
  apply (sum_le_sum (fun j _ => heat_sq_le_at_one ht (signedColumn n c d j))).trans
  simpa only [Real.one_rpow, mul_one] using hh

theorem negativeEnergy_le_L2 {κ Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    StepInput.negativeEnergy κ Λ ρ f ≤ Λ ^ (-ρ) * ‖f‖ ^ 2 := by
  have hb (z : ℤ) : (massiveWeight κ Λ ρ z)⁻¹ ≤ Λ ^ (-ρ) := by
    unfold massiveWeight
    rw [← Real.rpow_neg (by positivity : 0 ≤ Λ + (κ * (z : ℝ)) ^ 2)]
    exact Real.rpow_le_rpow_of_nonpos hΛ (le_add_of_nonneg_right (sq_nonneg _)) (neg_nonpos.mpr hρ)
  rw [StepInput.negativeEnergy, weightedFourierSq, norm_sq_fourier, ← tsum_mul_left]
  exact (StepInput.negativeEnergy_summable hΛ hρ f).tsum_le_tsum
    (fun z => mul_le_mul_of_nonneg_right (hb z) (sq_nonneg _))
    ((summable_fourier_sq f).mul_left _)

def negativeLinearMap (κ Λ ρ : ℝ) (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) : CircleL2 →ₗ[ℂ] FourierL2 where
  toFun f := WeightedHilbertSum.vector (fun z => (massiveWeight κ Λ ρ z)⁻¹)
    (fun z => inv_nonneg.mpr (massiveWeight_nonneg hΛ.le κ ρ z))
    (fourierBasis.repr f) (by
      simpa only [fourierBasis_repr] using StepInput.negativeEnergy_summable hΛ hρ f)
  map_add' f g := by
    apply lp.ext
    funext z
    change (Real.sqrt ((massiveWeight κ Λ ρ z)⁻¹) : ℂ) * fourierBasis.repr (f + g) z = _
    rw [map_add]
    change (Real.sqrt ((massiveWeight κ Λ ρ z)⁻¹) : ℂ) *
      (fourierBasis.repr f z + fourierBasis.repr g z) = _
    exact mul_add _ _ _
  map_smul' c f := by
    apply lp.ext
    funext z
    change (Real.sqrt ((massiveWeight κ Λ ρ z)⁻¹) : ℂ) * fourierBasis.repr (c • f) z = _
    rw [map_smul]
    change (Real.sqrt ((massiveWeight κ Λ ρ z)⁻¹) : ℂ) * (c * fourierBasis.repr f z) =
      c * ((Real.sqrt ((massiveWeight κ Λ ρ z)⁻¹) : ℂ) * fourierBasis.repr f z)
    ring

theorem negativeLinearMap_norm_sq (κ Λ ρ : ℝ) (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    ‖negativeLinearMap κ Λ ρ hΛ hρ f‖ ^ 2 = StepInput.negativeEnergy κ Λ ρ f := by
  calc
    _ = ∑' z : ℤ, (massiveWeight κ Λ ρ z)⁻¹ * ‖fourierBasis.repr f z‖ ^ 2 :=
      WeightedHilbertSum.vector_norm_sq (fun z => (massiveWeight κ Λ ρ z)⁻¹)
        (fun z => inv_nonneg.mpr (massiveWeight_nonneg hΛ.le κ ρ z))
        (fourierBasis.repr f) (by
          simpa only [fourierBasis_repr] using StepInput.negativeEnergy_summable hΛ hρ f)
    _ = _ := by simp only [StepInput.negativeEnergy, weightedFourierSq, fourierBasis_repr]

def negativeOperator (κ Λ ρ : ℝ) (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) : CircleL2 →L[ℂ] FourierL2 :=
  (negativeLinearMap κ Λ ρ hΛ hρ).mkContinuous (Real.sqrt (Λ ^ (-ρ))) (fun f => by
    have hh := negativeEnergy_le_L2 (κ := κ) hΛ hρ f
    rw [← negativeLinearMap_norm_sq κ Λ ρ hΛ hρ f] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact hh)

/-- The actual massive negative input energy is a continuous functional on
circle `L²`; it is the squared norm of a bounded Fourier multiplier. -/
theorem continuous_negativeEnergy {κ Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) :
    Continuous (StepInput.negativeEnergy κ Λ ρ : CircleL2 → ℝ) := by
  have heq : (StepInput.negativeEnergy κ Λ ρ : CircleL2 → ℝ) =
      (fun f => ‖negativeOperator κ Λ ρ hΛ hρ f‖ ^ 2) := by
    funext f
    change StepInput.negativeEnergy κ Λ ρ f = ‖negativeLinearMap κ Λ ρ hΛ hρ f‖ ^ 2
    exact (negativeLinearMap_norm_sq κ Λ ρ hΛ hρ f).symm
  rw [heq]
  exact (negativeOperator κ Λ ρ hΛ hρ).continuous.norm.pow 2

/-- A uniform physical Hilbert--Schmidt bound passes to any actual
columnwise circle-`L²` limit. The bound sequence may also converge, as
happens when coefficient approximations converge in the negative norm. -/
theorem infinite_HS_of_column_limits
    (u : ℕ → ℕ → CircleL2) (v : ℕ → CircleL2) (B : ℕ → ℝ) (Blim : ℝ)
    (hu : ∀ i, Filter.Tendsto (fun N => u N i) Filter.atTop (nhds (v i)))
    (hB : Filter.Tendsto B Filter.atTop (nhds Blim))
    (hbound : ∀ N, (∑ i ∈ range N, ‖u N i‖ ^ 2) ≤ B N) :
    Summable (fun i => ‖v i‖ ^ 2) ∧ (∑' i, ‖v i‖ ^ 2) ≤ Blim := by
  have hfinite (s : Finset ℕ) : (∑ i ∈ s, ‖v i‖ ^ 2) ≤ Blim := by
    have hlim : Filter.Tendsto (fun N => ∑ i ∈ s, ‖u N i‖ ^ 2)
        Filter.atTop (nhds (∑ i ∈ s, ‖v i‖ ^ 2)) := by
      exact tendsto_finsetSum s (fun i hi => (hu i).norm.pow 2)
    apply le_of_tendsto_of_tendsto hlim hB
    filter_upwards [Filter.eventually_ge_atTop (s.sup id + 1)] with N hN
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i hi hnot => sq_nonneg _)).trans (hbound N)
    intro i hi
    apply mem_range.mpr
    have hisup : i ≤ s.sup id := Finset.le_sup (f := id) hi
    omega
  have hs : Summable (fun i => ‖v i‖ ^ 2) := summable_of_sum_le (fun i => sq_nonneg _) hfinite
  exact ⟨hs, Real.tsum_le_of_sum_le (fun i => sq_nonneg _) hfinite⟩

theorem infinite_HS_of_growing_column_limits
    (cutoff : ℕ → ℕ) (hcutoff : Filter.Tendsto cutoff Filter.atTop Filter.atTop)
    (u : ℕ → ℕ → CircleL2) (v : ℕ → CircleL2) (B : ℕ → ℝ) (Blim : ℝ)
    (hu : ∀ i, Filter.Tendsto (fun N => u N i) Filter.atTop (nhds (v i)))
    (hB : Filter.Tendsto B Filter.atTop (nhds Blim))
    (hbound : ∀ N, (∑ i ∈ range (cutoff N), ‖u N i‖ ^ 2) ≤ B N) :
    Summable (fun i => ‖v i‖ ^ 2) ∧ (∑' i, ‖v i‖ ^ 2) ≤ Blim := by
  have hfinite (s : Finset ℕ) : (∑ i ∈ s, ‖v i‖ ^ 2) ≤ Blim := by
    have hlim : Filter.Tendsto (fun N => ∑ i ∈ s, ‖u N i‖ ^ 2)
        Filter.atTop (nhds (∑ i ∈ s, ‖v i‖ ^ 2)) :=
      tendsto_finsetSum s (fun i hi => (hu i).norm.pow 2)
    apply le_of_tendsto_of_tendsto hlim hB
    have hlarge := hcutoff.eventually (Filter.eventually_ge_atTop (s.sup id + 1))
    filter_upwards [hlarge] with N hN
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i hi hnot => sq_nonneg _)).trans (hbound N)
    intro i hi
    apply mem_range.mpr
    have hisup : i ≤ s.sup id := Finset.le_sup (f := id) hi
    omega
  have hs : Summable (fun i => ‖v i‖ ^ 2) := summable_of_sum_le (fun i => sq_nonneg _) hfinite
  exact ⟨hs, Real.tsum_le_of_sum_le (fun i => sq_nonneg _) hfinite⟩

/-- A finite weighted-Haar heat family, enumerated and padded by zero only
outside its actual finite input basis. -/
def paddedHeatedColumn (n : ℕ) (e : Fin (2 ^ n) ≃ Option (DetailIndex n))
    (c d : Grid n → ℝ) (t : ℝ) (i : ℕ) : CircleL2 :=
  if hi : i < 2 ^ n then heat t (signedColumn n c d (e ⟨i, hi⟩)) else 0

theorem paddedHeatedColumn_sum (n : ℕ) (e : Fin (2 ^ n) ≃ Option (DetailIndex n))
    (c d : Grid n → ℝ) (t : ℝ) :
    (∑ i ∈ range (2 ^ n), ‖paddedHeatedColumn n e c d t i‖ ^ 2) =
      ∑ j : Option (DetailIndex n), ‖heat t (signedColumn n c d j)‖ ^ 2 := by
  calc
    _ = ∑ i : Fin (2 ^ n), ‖heat t (signedColumn n c d (e i))‖ ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖paddedHeatedColumn n e c d t i‖ ^ 2)]
      apply sum_congr rfl
      intro i hi
      rw [paddedHeatedColumn, dite_eq_left i.isLt]
    _ = _ := Equiv.sum_comp e (fun j => ‖heat t (signedColumn n c d j)‖ ^ 2)

/-- The uniform signed finite-grid theorem passes to a genuine countable
physical heat-column limit. No infinite transport estimate is assumed:
the remaining hypotheses state only convergence of the actual coefficient
approximations and of the actual heated Haar columns. -/
theorem infinite_signed_heat_of_finite_grid_limits {t κ Λ ρ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 0 ≤ κ) (hΛ : 0 < Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n : ℕ → ℕ) (hn : Filter.Tendsto (fun N => 2 ^ n N) Filter.atTop Filter.atTop)
    (e : ∀ N, Fin (2 ^ n N) ≃ Option (DetailIndex (n N)))
    (c d : ∀ N, Grid (n N) → ℝ) (m U : ℝ) (hm : 0 < m)
    (hc : ∀ N x, m ≤ c N x ∧ c N x ≤ U) (hd : ∀ N x, m ≤ d N x ∧ d N x ≤ U)
    (f : CircleL2) (v : ℕ → CircleL2)
    (hf : Filter.Tendsto (fun N => gridStep (n N) (c N - d N)) Filter.atTop (nhds f))
    (hv : ∀ i, Filter.Tendsto (fun N => paddedHeatedColumn (n N) (e N) (c N) (d N) t i)
      Filter.atTop (nhds (v i))) :
    Summable (fun i => ‖v i‖ ^ 2) ∧
      (∑' i, ‖v i‖ ^ 2) ≤ signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ f *
        (Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)) := by
  let T := Λ ^ ρ * t ^ (-(1 / 2 : ℝ)) + t ^ (-(1 / 2 : ℝ) - ρ)
  let B : ℕ → ℝ := fun N => signedHeatSqConstant κ ρ m U *
    StepInput.negativeEnergy κ Λ ρ (gridStep (n N) (c N - d N)) * T
  have hB : Filter.Tendsto B Filter.atTop
      (nhds (signedHeatSqConstant κ ρ m U * StepInput.negativeEnergy κ Λ ρ f * T)) :=
    (((continuous_negativeEnergy hΛ hρ.le).tendsto f).comp hf).const_mul _ |>.mul_const T
  apply infinite_HS_of_growing_column_limits (fun N => 2 ^ n N) hn
    (fun N i => paddedHeatedColumn (n N) (e N) (c N) (d N) t i) v B _ hv hB
  intro N
  rw [paddedHeatedColumn_sum]
  exact signed_heat_finite_HS_sq ht ht1 hκ hΛ hρ hρhalf (n N) (c N) (d N) m U hm (hc N) (hd N)

@[fun_prop] theorem continuous_totalMass (n : ℕ) : Continuous (totalMass n : (Grid n → ℝ) → ℝ) := by
  unfold totalMass
  fun_prop

theorem continuousAt_detailColumn (n : ℕ) (a : Grid n → ℝ) (ha : ∀ x, 0 < a x)
    (i : DetailIndex n) (x : Grid n) :
    ContinuousAt (fun b : Grid n → ℝ => detailColumn n b i x) a := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    have hL : 0 < totalMass n (fun y => a (Sum.inl y)) := totalMass_pos n _ (fun y => ha (Sum.inl y))
    have hR : 0 < totalMass n (fun y => a (Sum.inr y)) := totalMass_pos n _ (fun y => ha (Sum.inr y))
    have cleft : Continuous (fun b : Grid (n + 1) → ℝ => fun y : Grid n => b (Sum.inl y)) :=
      continuous_pi (fun y => continuous_apply (Sum.inl y))
    have cright : Continuous (fun b : Grid (n + 1) → ℝ => fun y : Grid n => b (Sum.inr y)) :=
      continuous_pi (fun y => continuous_apply (Sum.inr y))
    have cL := ((continuous_totalMass n).comp cleft).continuousAt (x := a)
    have cR := ((continuous_totalMass n).comp cright).continuousAt (x := a)
    rcases i with ⟨⟩ | (i | i) <;> rcases x with x | x
    · simp only [detailColumn, Sum.elim_inl]
      unfold haarLeft haarMass
      exact ((cL.mul cR).div (cL.add cR) (add_pos hL hR).ne').sqrt.div cL hL.ne'
    · simp only [detailColumn, Sum.elim_inr]
      unfold haarRight haarMass
      exact ((cL.mul cR).div (cL.add cR) (add_pos hL hR).ne').sqrt.neg.div cR hR.ne'
    · simp only [detailColumn, Sum.elim_inl]
      change ContinuousAt ((fun b : Grid n → ℝ => detailColumn n b i x) ∘
        (fun b : Grid (n + 1) → ℝ => fun y => b (Sum.inl y))) a
      exact (ih (fun y => a (Sum.inl y)) (fun y => ha (Sum.inl y)) i x).comp cleft.continuousAt
    · simp only [detailColumn, Sum.elim_inr]
      exact continuousAt_const
    · simp only [detailColumn, Sum.elim_inl]
      exact continuousAt_const
    · simp only [detailColumn, Sum.elim_inr]
      change ContinuousAt ((fun b : Grid n → ℝ => detailColumn n b i x) ∘
        (fun b : Grid (n + 1) → ℝ => fun y => b (Sum.inr y))) a
      exact (ih (fun y => a (Sum.inr y)) (fun y => ha (Sum.inr y)) i x).comp cright.continuousAt

theorem continuousAt_haarColumn (n : ℕ) (a : Grid n → ℝ) (ha : ∀ x, 0 < a x)
    (i : Option (DetailIndex n)) (x : Grid n) :
    ContinuousAt (fun b : Grid n → ℝ => haarColumn n b i x) a := by
  cases i with
  | none =>
    simp only [haarColumn]
    have hp := totalMass_pos n a ha
    exact (continuous_totalMass n).continuousAt.sqrt.inv₀ (by positivity)
  | some i => exact continuousAt_detailColumn n a ha i x

def cellIndex (n : ℕ) (x : AddCircle (1 : ℝ)) : ZMod (2 ^ n) :=
  (((⌈(((2 ^ n : ℕ) : ℝ)) * ((AddCircle.equivIoc (1 : ℝ) 0 x : ℝ))⌉ - 1 : ℤ) : ZMod (2 ^ n)))

theorem measurable_cellIndex (n : ℕ) : Measurable (cellIndex n) := by
  have hm : Measurable (fun x : AddCircle (1 : ℝ) => (AddCircle.equivIoc (1 : ℝ) 0 x : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (T := (1 : ℝ)) 0).measurable_toFun
  exact (measurable_of_countable (fun z : ℤ => (z : ZMod (2 ^ n)))).comp
    (((measurable_const.mul hm).ceil).sub_const 1)

def cellSet (n : ℕ) (x : Grid n) : Set (AddCircle (1 : ℝ)) :=
  (cellIndex n) ⁻¹' {gridCellEquiv n x}

theorem measurableSet_cellSet (n : ℕ) (x : Grid n) : MeasurableSet (cellSet n x) :=
  (measurable_cellIndex n) (measurableSet_singleton _)

def cellRestrictionLinear (n : ℕ) (x : Grid n) : CircleL2 →ₗ[ℂ] CircleL2 where
  toFun f := (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f)).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp (f + g))),
      MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f)),
      MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp g)),
      Lp.coeFn_add f g, Lp.coeFn_add
        ((MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f)).toLp _)
        ((MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp g)).toLp _)] with y hfg hf hg ha hb
    rw [hfg, hb]
    simp only [Pi.add_apply, hf, hg]
    by_cases hy : y ∈ cellSet n x
    · simp only [Set.indicator_of_mem hy, Pi.add_apply, ha]
    · simp only [Set.indicator_of_notMem hy, add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp (c • f))),
      MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f)),
      Lp.coeFn_smul c f, Lp.coeFn_smul c
        ((MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f)).toLp _)] with y hcf hf ha hb
    simp only [RingHom.id_apply]
    rw [hcf, hb]
    simp only [Pi.smul_apply, hf]
    by_cases hy : y ∈ cellSet n x
    · simp only [Set.indicator_of_mem hy, Pi.smul_apply, ha]
    · simp only [Set.indicator_of_notMem hy, smul_zero]

theorem cellRestrictionLinear_norm (n : ℕ) (x : Grid n) (f : CircleL2) :
    ‖cellRestrictionLinear n x f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have hh := MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f))
  filter_upwards [hh] with y hy
  change ‖((MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f)).toLp _) y‖ ≤ _
  rw [hy]
  by_cases hmem : y ∈ cellSet n x
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, norm_zero]
    exact norm_nonneg _

def cellRestriction (n : ℕ) (x : Grid n) : CircleL2 →L[ℂ] CircleL2 :=
  (cellRestrictionLinear n x).mkContinuous 1 (fun f => by simpa using cellRestrictionLinear_norm n x f)

/-- Actual local coefficient averages, as continuous functionals on circle
`L²`; the indicator is the literal normalized dyadic cell field. -/
def localAverage (n : ℕ) (f : CircleL2) (x : Grid n) : ℝ :=
  (((2 ^ n : ℕ) : ℝ)) * (inner ℂ (gridStep n (Pi.single x 1)) f).re

theorem continuous_localAverage (n : ℕ) : Continuous (localAverage n : CircleL2 → (Grid n → ℝ)) := by
  apply continuous_pi
  intro x
  unfold localAverage
  fun_prop

/-- The actual weighted Haar factor column attached to a fixed finite
dyadic node, now for an arbitrary circle-`L²` coefficient field. -/
def fixedHaarColumn (n : ℕ) (i : Option (DetailIndex n)) (f : CircleL2) : CircleL2 :=
  ∑ x : Grid n, (Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (localAverage n f) i x) •
    cellRestriction n x f

theorem continuousAt_fixedHaarColumn (n : ℕ) (i : Option (DetailIndex n)) (f : CircleL2)
    (hf : ∀ x, 0 < localAverage n f x) : ContinuousAt (fixedHaarColumn n i) f := by
  unfold fixedHaarColumn
  apply tendsto_finsetSum
  intro x hx
  have hc : ContinuousAt (fun b : CircleL2 => Real.sqrt (((2 ^ n : ℕ) : ℝ)) *
      haarColumn n (localAverage n b) i x) f :=
    continuousAt_const.mul ((continuousAt_haarColumn n (localAverage n f) hf i x).comp
      (continuous_localAverage n).continuousAt)
  exact hc.tendsto.smul (cellRestriction n x).continuous.continuousAt.tendsto

/-- Fixed actual Haar columns converge in physical `L²` whenever the
coefficient fields converge in `L²` and the limiting local masses are
positive. No heat smoothing or transport conclusion is assumed. -/
theorem fixedHaarColumn_tendsto (n : ℕ) (i : Option (DetailIndex n))
    (f : ℕ → CircleL2) (g : CircleL2)
    (hg : ∀ x, 0 < localAverage n g x)
    (hfg : Filter.Tendsto f Filter.atTop (nhds g)) :
    Filter.Tendsto (fun N => fixedHaarColumn n i (f N)) Filter.atTop (nhds (fixedHaarColumn n i g)) :=
  (continuousAt_fixedHaarColumn n i g hg).tendsto.comp hfg

theorem gridStep_ae_cellIndex (n : ℕ) (a : Grid n → ℝ) :
    gridStep n a =ᵐ[haarAddCircle] fun y => (a ((gridCellEquiv n).symm (cellIndex n y)) : ℂ) := by
  apply (stepLp_ae (2 ^ n) (fun j => a ((gridCellEquiv n).symm j))).trans
  apply ae_of_all
  intro y
  let z := AddCircle.equivIoc (1 : ℝ) 0 y
  have hz : (((z : ℝ) : AddCircle (1 : ℝ))) = y := AddCircle.coe_equivIoc
  calc
    _ = CircleStep.circleStep (2 ^ n) (fun j => a ((gridCellEquiv n).symm j))
        (((z : ℝ) : AddCircle (1 : ℝ))) := congrArg _ hz.symm
    _ = _ := rfl

theorem cellRestriction_ae (n : ℕ) (x : Grid n) (f : CircleL2) :
    cellRestriction n x f =ᵐ[haarAddCircle] (cellSet n x).indicator f :=
  MemLp.coeFn_toLp (MemLp.indicator (measurableSet_cellSet n x).nullMeasurableSet (Lp.memLp f))

theorem cellRestriction_gridStep (n : ℕ) (x : Grid n) (a : Grid n → ℝ) :
    cellRestriction n x (gridStep n a) = gridStep n (Pi.single x (a x)) := by
  apply Lp.ext
  filter_upwards [cellRestriction_ae n x (gridStep n a), gridStep_ae_cellIndex n a,
    gridStep_ae_cellIndex n (Pi.single x (a x))] with y hr ha hs
  rw [hr, hs]
  by_cases hy : y ∈ cellSet n x
  · have hidx : cellIndex n y = gridCellEquiv n x := hy
    have hcoord : (gridCellEquiv n).symm (cellIndex n y) = x := by rw [hidx, Equiv.symm_apply_apply]
    rw [Set.indicator_of_mem hy, ha, hcoord, Pi.single_eq_same]
  · have hcoord : (gridCellEquiv n).symm (cellIndex n y) ≠ x := by
      intro heq
      apply hy
      change cellIndex n y = gridCellEquiv n x
      rw [← heq, Equiv.apply_symm_apply]
    rw [Set.indicator_of_notMem hy, Pi.single_eq_of_ne hcoord]
    rfl

theorem localAverage_gridStep (n : ℕ) (a : Grid n → ℝ) : localAverage n (gridStep n a) = a := by
  funext x
  rw [localAverage, gridStep_inner]
  have hsum : (∑ y : Grid n, ((Pi.single x (1 : ℝ) : Grid n → ℝ) y) * a y) = a x := by
    simp [Pi.single_apply]
  rw [hsum, ← mul_assoc, mul_inv_cancel₀ (by positivity : (((2 ^ n : ℕ) : ℝ)) ≠ 0), one_mul]

def gridStepLinear (n : ℕ) : (Grid n → ℝ) →ₗ[ℝ] CircleL2 where
  toFun := gridStep n
  map_add' := gridStep_add n
  map_smul' c f := by
    change gridStep n (c • f) = c • gridStep n f
    unfold gridStep
    rw [← stepLp_smul]
    rfl

/-- The arbitrary-coefficient fixed-node definition agrees exactly with
the explicitly constructed weighted Haar factor on every matching finite
dyadic grid. -/
theorem fixedHaarColumn_gridStep (n : ℕ) (i : Option (DetailIndex n)) (a : Grid n → ℝ) :
    fixedHaarColumn n i (gridStep n a) =
      gridStep n (fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * localFactor n a x i) := by
  unfold fixedHaarColumn
  simp_rw [localAverage_gridStep, cellRestriction_gridStep]
  let q : Grid n → ℝ := fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n a i x
  have hlin := map_sum (gridStepLinear n) (fun x => q x • Pi.single x (a x)) Finset.univ
  have hsmul (x : Grid n) : gridStepLinear n (q x • Pi.single x (a x)) =
      q x • gridStep n (Pi.single x (a x)) := map_smul (gridStepLinear n) _ _
  simp_rw [hsmul] at hlin
  change gridStep n (∑ x, q x • Pi.single x (a x)) = ∑ x, q x • gridStep n (Pi.single x (a x)) at hlin
  change (∑ x, q x • gridStep n (Pi.single x (a x))) = _
  rw [← hlin]
  apply congrArg (gridStep n)
  funext y
  rw [Finset.sum_apply]
  have hsum : (∑ x : Grid n, (q x • Pi.single x (a x)) y) = q y * a y := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [sum_eq_single y]
    · rw [Pi.single_eq_same]
    · intro x hx hxy
      rw [Pi.single_eq_of_ne (Ne.symm hxy), mul_zero]
    · simp
  rw [hsum, localFactor_apply]
  dsimp only [q]
  ring

theorem fixedHaarColumn_tendsto_of_uniform_localAverage (n : ℕ) (i : Option (DetailIndex n))
    (f : ℕ → CircleL2) (g : CircleL2) (m : ℝ) (hm : 0 < m)
    (hf : ∀ N x, m ≤ localAverage n (f N) x)
    (hfg : Filter.Tendsto f Filter.atTop (nhds g)) :
    Filter.Tendsto (fun N => fixedHaarColumn n i (f N)) Filter.atTop (nhds (fixedHaarColumn n i g)) := by
  apply fixedHaarColumn_tendsto n i f g _ hfg
  intro x
  have hlim := (((continuous_apply x).comp (continuous_localAverage n)).tendsto g).comp hfg
  have hle : m ≤ localAverage n g x :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall (fun N => hf N x))
  exact hm.trans_le hle

/-- The fixed-node physical column definition agrees with the signed finite
factor columns, rather than merely sharing a covariance or norm bound. -/
theorem signedColumn_fixedHaar (n : ℕ) (c d : Grid n → ℝ) (i : Option (DetailIndex n)) :
    signedColumn n c d i = fixedHaarColumn n i (gridStep n c) - fixedHaarColumn n i (gridStep n d) := by
  rw [fixedHaarColumn_gridStep, fixedHaarColumn_gridStep, ← gridStep_sub]
  have hgrid : signedColumn n c d i =
      gridStep n (fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * (localFactor n c x i - localFactor n d x i)) := by
    apply Lp.ext
    exact (signedColumn_ae n c d i).trans (stepLp_ae (2 ^ n) (fun k =>
      Real.sqrt (((2 ^ n : ℕ) : ℝ)) * (localFactor n c ((gridCellEquiv n).symm k) i -
        localFactor n d ((gridCellEquiv n).symm k) i))).symm
  rw [hgrid]
  apply congrArg (gridStep n)
  funext x
  dsimp only [Pi.sub_apply]
  ring

/-- Convergence of actual heated signed weighted-Haar columns for arbitrary
coefficient fields, with local masses computed by genuine continuous cell
averages. This is the fixed-column ingredient of the infinite passage. -/
theorem heated_fixed_signed_columns_tendsto (n : ℕ) (i : Option (DetailIndex n)) (t : ℝ)
    (c d : ℕ → CircleL2) (f g : CircleL2)
    (hf : ∀ x, 0 < localAverage n f x) (hg : ∀ x, 0 < localAverage n g x)
    (hc : Filter.Tendsto c Filter.atTop (nhds f)) (hd : Filter.Tendsto d Filter.atTop (nhds g)) :
    Filter.Tendsto (fun N => heat t (fixedHaarColumn n i (c N) - fixedHaarColumn n i (d N)))
      Filter.atTop (nhds (heat t (fixedHaarColumn n i f - fixedHaarColumn n i g))) := by
  exact (heat t).continuous.continuousAt.tendsto.comp
    ((fixedHaarColumn_tendsto n i c f hf hc).sub (fixedHaarColumn_tendsto n i d g hg hd))

theorem totalMass_parentAverage (n : ℕ) (a : Grid (n + 1) → ℝ) :
    totalMass (n + 1) a = 2 * totalMass n (parentAverage n a) := by
  unfold totalMass
  erw [sum_leafChildren n]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x hx
  unfold parentAverage
  ring

theorem parentAverage_pos (n : ℕ) (a : Grid (n + 1) → ℝ) (ha : ∀ x, 0 < a x) :
    ∀ x, 0 < parentAverage n a x := by
  intro x
  unfold parentAverage
  exact div_pos (add_pos (ha _) (ha _)) (by norm_num)

theorem haarMass_double {l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    haarMass (2 * l) (2 * r) = Real.sqrt 2 * haarMass l r := by
  have heq : (2 * l * (2 * r)) / (2 * l + 2 * r) = 2 * (l * r / (l + r)) := by
    field_simp
  unfold haarMass
  rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem sqrt_two_half_inv : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem haarLeft_double {l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    haarLeft (2 * l) (2 * r) = (Real.sqrt 2)⁻¹ * haarLeft l r := by
  unfold haarLeft
  rw [haarMass_double hl hr]
  calc
    _ = (Real.sqrt 2 / 2) * (haarMass l r / l) := by field_simp
    _ = _ := by rw [sqrt_two_half_inv]

theorem haarRight_double {l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    haarRight (2 * l) (2 * r) = (Real.sqrt 2)⁻¹ * haarRight l r := by
  unfold haarRight
  rw [haarMass_double hl hr]
  calc
    _ = (Real.sqrt 2 / 2) * (-haarMass l r / r) := by field_simp
    _ = _ := by rw [sqrt_two_half_inv]

/-- Exact weighted-Haar refinement for an arbitrary positive fine
coefficient: older Haar functions depend only on the true parent averages,
including the required counting-to-physical normalization. -/
theorem detailColumn_parentAverage (n : ℕ) (a : Grid (n + 1) → ℝ) (ha : ∀ x, 0 < a x)
    (i : DetailIndex n) (x : Grid (n + 1)) :
    detailColumn (n + 1) a (detailEmbed n i) x =
      (Real.sqrt 2)⁻¹ * detailColumn n (parentAverage n a) i (leafParent n x) := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    have hal : ∀ x, 0 < a (Sum.inl x) := fun x => ha (Sum.inl x)
    have har : ∀ x, 0 < a (Sum.inr x) := fun x => ha (Sum.inr x)
    have hl : 0 < totalMass n (parentAverage n (fun y => a (Sum.inl y))) :=
      totalMass_pos n _ (parentAverage_pos n _ hal)
    have hr : 0 < totalMass n (parentAverage n (fun y => a (Sum.inr y))) :=
      totalMass_pos n _ (parentAverage_pos n _ har)
    rcases i with ⟨⟩ | (i | i) <;> rcases x with x | x
    · simp only [detailEmbed, detailColumn, Sum.elim_inl, leafParent]
      change haarLeft (totalMass (n + 1) (fun y => a (Sum.inl y)))
        (totalMass (n + 1) (fun y => a (Sum.inr y))) =
          (Real.sqrt 2)⁻¹ * haarLeft
            (totalMass n (parentAverage n (fun y => a (Sum.inl y))))
            (totalMass n (parentAverage n (fun y => a (Sum.inr y))))
      rw [totalMass_parentAverage, totalMass_parentAverage]
      exact haarLeft_double hl hr
    · simp only [detailEmbed, detailColumn, Sum.elim_inr, leafParent]
      change haarRight (totalMass (n + 1) (fun y => a (Sum.inl y)))
        (totalMass (n + 1) (fun y => a (Sum.inr y))) =
          (Real.sqrt 2)⁻¹ * haarRight
            (totalMass n (parentAverage n (fun y => a (Sum.inl y))))
            (totalMass n (parentAverage n (fun y => a (Sum.inr y))))
      rw [totalMass_parentAverage, totalMass_parentAverage]
      exact haarRight_double hl hr
    · simp only [detailEmbed, detailColumn, Sum.elim_inl, leafParent]
      have hp : (fun y => parentAverage (n + 1) a (Sum.inl y)) =
          parentAverage n (fun y => a (Sum.inl y)) := by funext y; rfl
      rw [hp]
      exact ih _ hal i x
    · simp only [detailEmbed, detailColumn, Sum.elim_inr, leafParent, mul_zero]
    · simp only [detailEmbed, detailColumn, Sum.elim_inl, leafParent, mul_zero]
    · simp only [detailEmbed, detailColumn, Sum.elim_inr, leafParent]
      have hp : (fun y => parentAverage (n + 1) a (Sum.inr y)) =
          parentAverage n (fun y => a (Sum.inr y)) := by funext y; rfl
      rw [hp]
      exact ih _ har i x

theorem haarColumn_parentAverage (n : ℕ) (a : Grid (n + 1) → ℝ) (ha : ∀ x, 0 < a x)
    (i : Option (DetailIndex n)) (x : Grid (n + 1)) :
    haarColumn (n + 1) a (modeEmbed n i) x =
      (Real.sqrt 2)⁻¹ * haarColumn n (parentAverage n a) i (leafParent n x) := by
  cases i with
  | none =>
    simp only [modeEmbed, haarColumn]
    rw [totalMass_parentAverage, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), _root_.mul_inv_rev, mul_comm]
  | some i => exact detailColumn_parentAverage n a ha i x

theorem localAverage_parent_gridStep (n : ℕ) (a : Grid (n + 1) → ℝ) :
    localAverage n (gridStep (n + 1) a) = parentAverage n a := by
  funext x
  rw [localAverage, ← gridStep_parent n (Pi.single x 1), gridStep_inner]
  have hsum : (∑ y : Grid (n + 1),
      ((fun z : Grid n => (Pi.single x (1 : ℝ) : Grid n → ℝ) z) (leafParent n y)) * a y) =
      2 * parentAverage n a x := by
    calc
      _ = ∑ y : Grid (n + 1), a y * ((Pi.single x (1 : ℝ) : Grid n → ℝ) (leafParent n y)) := by
        apply sum_congr rfl
        intro y hy
        ring
      _ = 2 * ∑ z : Grid n, parentAverage n a z * ((Pi.single x (1 : ℝ) : Grid n → ℝ) z) :=
        sum_parent_pullback n a _
      _ = _ := by simp [Pi.single_apply]
  dsimp only at hsum
  erw [hsum]
  have hD : (((2 ^ (n + 1) : ℕ) : ℝ)) = 2 * (((2 ^ n : ℕ) : ℝ)) := by
    simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hD]
  field_simp

/-- Pointwise physical factor compatibility with true parent averages,
for every positive fine-grid coefficient and every older input column. -/
theorem physical_localFactor_parent (n : ℕ) (a : Grid (n + 1) → ℝ) (ha : ∀ x, 0 < a x)
    (i : Option (DetailIndex n)) (x : Grid (n + 1)) :
    Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)) * localFactor (n + 1) a x (modeEmbed n i) =
      a x * (Real.sqrt (((2 ^ n : ℕ) : ℝ)) *
        haarColumn n (parentAverage n a) i (leafParent n x)) := by
  rw [localFactor_apply, haarColumn_parentAverage n a ha, sqrt_grid_succ]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

theorem cellSet_iff (n : ℕ) (x : Grid n) (y : AddCircle (1 : ℝ)) :
    y ∈ cellSet n x ↔ (gridCellEquiv n).symm (cellIndex n y) = x := by
  change cellIndex n y = gridCellEquiv n x ↔ _
  constructor
  · intro h
    rw [h, Equiv.symm_apply_apply]
  · intro h
    calc
      _ = gridCellEquiv n ((gridCellEquiv n).symm (cellIndex n y)) := (Equiv.apply_symm_apply _ _).symm
      _ = _ := congrArg (gridCellEquiv n) h

theorem cellRestriction_parent_gridStep (n : ℕ) (x : Grid n) (a : Grid (n + 1) → ℝ) :
    cellRestriction n x (gridStep (n + 1) a) =
      gridStep (n + 1) (fun y => if leafParent n y = x then a y else 0) := by
  apply Lp.ext
  have hI := gridStep_ae_cellIndex (n + 1) (fun y => (Pi.single x (1 : ℝ) : Grid n → ℝ) (leafParent n y))
  rw [gridStep_parent] at hI
  filter_upwards [cellRestriction_ae n x (gridStep (n + 1) a), gridStep_ae_cellIndex (n + 1) a,
    gridStep_ae_cellIndex n (Pi.single x (1 : ℝ)), hI,
    gridStep_ae_cellIndex (n + 1) (fun y => if leafParent n y = x then a y else 0)] with y hr ha hi hj ht
  rw [hr, ht]
  have heq := hi.symm.trans hj
  have hmem : y ∈ cellSet n x ↔ leafParent n ((gridCellEquiv (n + 1)).symm (cellIndex (n + 1) y)) = x := by
    rw [cellSet_iff]
    constructor
    · intro hc
      by_contra hp
      simp [hc, hp] at heq
    · intro hp
      by_contra hc
      simp [hc, hp] at heq
  by_cases hp : leafParent n ((gridCellEquiv (n + 1)).symm (cellIndex (n + 1) y)) = x
  · rw [Set.indicator_of_mem (hmem.mpr hp), ha]
    simp only [hp, ite_true]
  · rw [Set.indicator_of_notMem (fun hy => hp (hmem.mp hy))]
    simp only [hp, ite_false, Complex.ofReal_zero]

/-- One-step identification of an older weighted-Haar physical column
inside an arbitrary finer coefficient grid with the actual fixed-node
column map used in the convergence theorem. -/
theorem fixedHaarColumn_parent_gridStep (n : ℕ) (i : Option (DetailIndex n))
    (a : Grid (n + 1) → ℝ) (ha : ∀ x, 0 < a x) :
    fixedHaarColumn n i (gridStep (n + 1) a) =
      gridStep (n + 1) (fun y => Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)) *
        localFactor (n + 1) a y (modeEmbed n i)) := by
  unfold fixedHaarColumn
  simp_rw [localAverage_parent_gridStep, cellRestriction_parent_gridStep]
  let q : Grid n → ℝ := fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (parentAverage n a) i x
  have hlin := map_sum (gridStepLinear (n + 1))
    (fun x : Grid n => q x • (fun y : Grid (n + 1) => if leafParent n y = x then a y else 0)) Finset.univ
  simp only [map_smul] at hlin
  change gridStep (n + 1) (∑ x : Grid n, q x • (fun y : Grid (n + 1) => if leafParent n y = x then a y else 0)) =
    ∑ x : Grid n, q x • gridStep (n + 1) (fun y => if leafParent n y = x then a y else 0) at hlin
  change (∑ x : Grid n, q x • gridStep (n + 1) (fun y => if leafParent n y = x then a y else 0)) = _
  rw [← hlin]
  apply congrArg (gridStep (n + 1))
  funext y
  rw [Finset.sum_apply]
  have hsum : (∑ x : Grid n, (q x • (fun z : Grid (n + 1) => if leafParent n z = x then a z else 0)) y) =
      q (leafParent n y) * a y := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [sum_eq_single (leafParent n y)]
    · simp
    · intro x hx hxy
      rw [ite_eq_right (Ne.symm hxy), mul_zero]
    · simp
  rw [hsum, physical_localFactor_parent n a ha]
  dsimp only [q]
  ring

def modeLift (n : ℕ) : (r : ℕ) → Option (DetailIndex n) → Option (DetailIndex (n + r))
  | 0, i => i
  | r + 1, i => modeEmbed (n + r) (modeLift n r i)

def ancestorLeaf (n : ℕ) : (r : ℕ) → Grid (n + r) → Grid n
  | 0, x => x
  | r + 1, x => ancestorLeaf n r (leafParent (n + r) x)

def ancestorAverage (n : ℕ) : (r : ℕ) → (Grid (n + r) → ℝ) → Grid n → ℝ
  | 0, a => a
  | r + 1, a => ancestorAverage n r (parentAverage (n + r) a)

theorem normalized_weighted_haar_parent (n : ℕ) (a : Grid (n + 1) → ℝ) (ha : ∀ x, 0 < a x)
    (i : Option (DetailIndex n)) (x : Grid (n + 1)) :
    Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)) * haarColumn (n + 1) a (modeEmbed n i) x =
      Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (parentAverage n a) i (leafParent n x) := by
  rw [haarColumn_parentAverage n a ha, sqrt_grid_succ]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- Exact arbitrary-resolution weighted-Haar prefix identification at the
cell level: a fixed older input mode uses only its genuine ancestral
coefficient averages, while retaining the actual fine coefficient in the
physical factor column. -/
theorem weighted_haar_all_refinements (n r : ℕ) (a : Grid (n + r) → ℝ)
    (ha : ∀ x, 0 < a x) (i : Option (DetailIndex n)) (x : Grid (n + r)) :
    Real.sqrt (((2 ^ (n + r) : ℕ) : ℝ)) * haarColumn (n + r) a (modeLift n r i) x =
      Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (ancestorAverage n r a) i (ancestorLeaf n r x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    calc
      _ = Real.sqrt (((2 ^ (n + r) : ℕ) : ℝ)) * haarColumn (n + r)
          (parentAverage (n + r) a) (modeLift n r i) (leafParent (n + r) x) :=
        normalized_weighted_haar_parent (n + r) a ha (modeLift n r i) x
      _ = _ := ih _ (parentAverage_pos (n + r) a ha) (leafParent (n + r) x)

theorem physical_factor_all_refinements (n r : ℕ) (a : Grid (n + r) → ℝ)
    (ha : ∀ x, 0 < a x) (i : Option (DetailIndex n)) (x : Grid (n + r)) :
    Real.sqrt (((2 ^ (n + r) : ℕ) : ℝ)) * localFactor (n + r) a x (modeLift n r i) =
      a x * (Real.sqrt (((2 ^ n : ℕ) : ℝ)) *
        haarColumn n (ancestorAverage n r a) i (ancestorLeaf n r x)) := by
  rw [localFactor_apply]
  calc
    _ = a x * (Real.sqrt (((2 ^ (n + r) : ℕ) : ℝ)) * haarColumn (n + r) a (modeLift n r i) x) := by ring
    _ = _ := by rw [weighted_haar_all_refinements n r a ha]

/-- Literal dyadic local averaging is order preserving on the real parts
of arbitrary circle `L²` coefficient fields. -/
theorem localAverage_mono_ae (n : ℕ) (f g : CircleL2)
    (hfg : ∀ᵐ y ∂haarAddCircle, (f y).re ≤ (g y).re) (x : Grid n) :
    localAverage n f x ≤ localAverage n g x := by
  let I : CircleL2 := gridStep n (Pi.single x 1)
  have hi := gridStep_ae_cellIndex n (Pi.single x (1 : ℝ))
  have hp : ∀ᵐ y ∂haarAddCircle,
      (inner ℂ (I y) (f y)).re ≤ (inner ℂ (I y) (g y)).re := by
    filter_upwards [hi, hfg] with y hy hle
    change (gridStep n (Pi.single x 1)) y = _ at hy
    change (inner ℂ ((gridStep n (Pi.single x 1)) y) (f y)).re ≤
      (inner ℂ ((gridStep n (Pi.single x 1)) y) (g y)).re
    rw [hy]
    by_cases h : (gridCellEquiv n).symm (cellIndex n y) = x
    · simpa [Pi.single_apply, h, RCLike.inner_apply] using hle
    · simp [h, RCLike.inner_apply]
  have hf := L2.integrable_inner (𝕜 := ℂ) I f
  have hg := L2.integrable_inner (𝕜 := ℂ) I g
  have hh := integral_mono_ae hf.re hg.re hp
  rw [integral_re hf, integral_re hg, ← L2.inner_def, ← L2.inner_def] at hh
  exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- Actual almost-everywhere coefficient bounds give the same bounds on
every local cell average, with no positivity-of-masses premise. -/
theorem localAverage_bounds_ae (n : ℕ) (f : CircleL2) (m U : ℝ)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (x : Grid n) :
    m ≤ localAverage n f x ∧ localAverage n f x ≤ U := by
  have hlo : ∀ᵐ y ∂haarAddCircle, (gridStep n (fun _ => m) y).re ≤ (f y).re := by
    filter_upwards [gridStep_ae_cellIndex n (fun _ => m), hf] with y hy hb
    simpa [hy] using hb.1
  have hup : ∀ᵐ y ∂haarAddCircle, (f y).re ≤ (gridStep n (fun _ => U) y).re := by
    filter_upwards [gridStep_ae_cellIndex n (fun _ => U), hf] with y hy hb
    simpa [hy] using hb.2
  constructor
  · simpa only [localAverage_gridStep] using localAverage_mono_ae n _ _ hlo x
  · simpa only [localAverage_gridStep] using localAverage_mono_ae n _ _ hup x

theorem fixedHaarColumn_tendsto_of_uniform_elliptic (n : ℕ) (i : Option (DetailIndex n))
    (f : ℕ → CircleL2) (g : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ N, ∀ᵐ y ∂haarAddCircle, m ≤ (f N y).re ∧ (f N y).re ≤ U)
    (hfg : Filter.Tendsto f Filter.atTop (nhds g)) :
    Filter.Tendsto (fun N => fixedHaarColumn n i (f N)) Filter.atTop (nhds (fixedHaarColumn n i g)) := by
  exact fixedHaarColumn_tendsto_of_uniform_localAverage n i f g m hm
    (fun N x => (localAverage_bounds_ae n (f N) m U (hf N) x).1) hfg

/-- Ordinary dyadic cell fields refine exactly at every depth. -/
theorem gridStep_ancestor (n r : ℕ) (a : Grid n → ℝ) :
    gridStep (n + r) (fun y => a (ancestorLeaf n r y)) = gridStep n a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    calc
      _ = gridStep (n + r) (fun y => a (ancestorLeaf n r y)) :=
        gridStep_parent (n + r) _
      _ = _ := ih

theorem sum_ancestor_pullback (n r : ℕ) (a : Grid (n + r) → ℝ) (b : Grid n → ℝ) :
    (∑ y, a y * b (ancestorLeaf n r y)) = (2 : ℝ) ^ r * ∑ x, ancestorAverage n r a x * b x := by
  induction r with
  | zero => simp [ancestorLeaf, ancestorAverage]
  | succ r ih =>
    calc
      _ = 2 * ∑ y : Grid (n + r), parentAverage (n + r) a y * b (ancestorLeaf n r y) :=
        sum_parent_pullback (n + r) a _
      _ = 2 * ((2 : ℝ) ^ r * ∑ x, ancestorAverage n r (parentAverage (n + r) a) x * b x) := by rw [ih]
      _ = _ := by simp only [ancestorAverage, pow_succ]; ring

theorem localAverage_ancestor_gridStep (n r : ℕ) (a : Grid (n + r) → ℝ) :
    localAverage n (gridStep (n + r) a) = ancestorAverage n r a := by
  funext x
  rw [localAverage, ← gridStep_ancestor n r (Pi.single x 1), gridStep_inner]
  have hsum : (∑ y : Grid (n + r),
      ((Pi.single x (1 : ℝ) : Grid n → ℝ) (ancestorLeaf n r y)) * a y) =
      (2 : ℝ) ^ r * ancestorAverage n r a x := by
    calc
      _ = ∑ y : Grid (n + r), a y * ((Pi.single x (1 : ℝ) : Grid n → ℝ) (ancestorLeaf n r y)) := by
        apply sum_congr rfl
        intro y hy
        ring
      _ = (2 : ℝ) ^ r * ∑ z : Grid n, ancestorAverage n r a z * ((Pi.single x (1 : ℝ) : Grid n → ℝ) z) :=
        sum_ancestor_pullback n r a _
      _ = _ := by simp [Pi.single_apply]
  erw [hsum]
  simp only [Nat.cast_pow, Nat.cast_ofNat, pow_add, Nat.cast_mul]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hr : (2 : ℝ) ^ r ≠ 0 := by positivity
  field_simp

theorem cellRestriction_ancestor_gridStep (n r : ℕ) (x : Grid n) (a : Grid (n + r) → ℝ) :
    cellRestriction n x (gridStep (n + r) a) =
      gridStep (n + r) (fun y => if ancestorLeaf n r y = x then a y else 0) := by
  apply Lp.ext
  have hI := gridStep_ae_cellIndex (n + r) (fun y => (Pi.single x (1 : ℝ) : Grid n → ℝ) (ancestorLeaf n r y))
  rw [gridStep_ancestor] at hI
  filter_upwards [cellRestriction_ae n x (gridStep (n + r) a), gridStep_ae_cellIndex (n + r) a,
    gridStep_ae_cellIndex n (Pi.single x (1 : ℝ)), hI,
    gridStep_ae_cellIndex (n + r) (fun y => if ancestorLeaf n r y = x then a y else 0)] with y hr ha hi hj ht
  rw [hr, ht]
  have heq := hi.symm.trans hj
  have hmem : y ∈ cellSet n x ↔ ancestorLeaf n r ((gridCellEquiv (n + r)).symm (cellIndex (n + r) y)) = x := by
    rw [cellSet_iff]
    constructor
    · intro hc
      by_contra hp
      simp [hc, hp] at heq
    · intro hp
      by_contra hc
      simp [hc, hp] at heq
  by_cases hp : ancestorLeaf n r ((gridCellEquiv (n + r)).symm (cellIndex (n + r) y)) = x
  · rw [Set.indicator_of_mem (hmem.mpr hp), ha]
    simp only [hp, ite_true]
  · rw [Set.indicator_of_notMem (fun hy => hp (hmem.mp hy))]
    simp only [hp, ite_false, Complex.ofReal_zero]

/-- The exact fixed-node column identification at arbitrary finer spatial
resolution, retaining the fine coefficient itself in the physical column. -/
theorem fixedHaarColumn_ancestor_gridStep (n r : ℕ) (i : Option (DetailIndex n))
    (a : Grid (n + r) → ℝ) (ha : ∀ x, 0 < a x) :
    fixedHaarColumn n i (gridStep (n + r) a) =
      gridStep (n + r) (fun y => Real.sqrt (((2 ^ (n + r) : ℕ) : ℝ)) *
        localFactor (n + r) a y (modeLift n r i)) := by
  unfold fixedHaarColumn
  simp_rw [localAverage_ancestor_gridStep, cellRestriction_ancestor_gridStep]
  let q : Grid n → ℝ := fun x => Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (ancestorAverage n r a) i x
  have hlin := map_sum (gridStepLinear (n + r))
    (fun x : Grid n => q x • (fun y : Grid (n + r) => if ancestorLeaf n r y = x then a y else 0)) Finset.univ
  simp only [map_smul] at hlin
  change gridStep (n + r) (∑ x : Grid n, q x • (fun y : Grid (n + r) => if ancestorLeaf n r y = x then a y else 0)) =
    ∑ x : Grid n, q x • gridStep (n + r) (fun y => if ancestorLeaf n r y = x then a y else 0) at hlin
  change (∑ x : Grid n, q x • gridStep (n + r) (fun y => if ancestorLeaf n r y = x then a y else 0)) = _
  rw [← hlin]
  apply congrArg (gridStep (n + r))
  funext y
  rw [Finset.sum_apply]
  have hsum : (∑ x : Grid n, (q x • (fun z : Grid (n + r) => if ancestorLeaf n r z = x then a z else 0)) y) =
      q (ancestorLeaf n r y) * a y := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [sum_eq_single (ancestorLeaf n r y)]
    · simp
    · intro x hx hxy
      rw [ite_eq_right (Ne.symm hxy), mul_zero]
    · simp
  rw [hsum, physical_factor_all_refinements n r a ha]
  dsimp only [q]
  ring

end SHE.FiniteHaar
