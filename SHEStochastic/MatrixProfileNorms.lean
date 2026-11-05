module

public import SHEStochastic.MatrixPhysicalColumnMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixProfileNorms
open MeasureTheory Matrix MatrixProfileHilbert MatrixPhysicalColumnMap
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

theorem size_matrix (v : Fiber d) : MatrixFrobeniusNorm.size (toMatrix d v)=‖v‖ := by
  rw [← norm_vector]
  exact congrArg norm ((coordinates d).symm_apply_apply v)

theorem column_bound (A : Matrix d d ℝ) (i : d) :
    ‖MatrixHaarRootColumns.column A i‖ ≤ MatrixFrobeniusNorm.size A := by
  apply (sq_le_sq₀ (norm_nonneg _) (MatrixFrobeniusNorm.nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, MatrixFrobeniusNorm.square]
  simp only [MatrixHaarRootColumns.column_apply, SHE.FiniteTransport.frobeniusSq]
  apply Finset.sum_le_sum
  intro p hp
  exact Finset.single_le_sum (fun q _ => sq_nonneg (A p q)) (Finset.mem_univ i)

/-- Constant right multiplication and component selection preserve the
Frobenius profile bound without a grid-dependent or dimension factor. -/
theorem action_bound (i : d) (u : Space d) (C : Matrix d d ℝ) :
    ‖action i u C‖ ≤ MatrixFrobeniusNorm.size C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [action_ae i u C] with x hx
  rw [hx]
  calc
    _ ≤ MatrixFrobeniusNorm.size (toMatrix d (u x)*C) := column_bound _ i
    _ ≤ MatrixFrobeniusNorm.size (toMatrix d (u x))*MatrixFrobeniusNorm.size C := MatrixFrobeniusNorm.mul _ _
    _ = _ := by rw [size_matrix, mul_comm]

theorem restriction_bound (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (u : Space d) :
    ‖restriction s hs u‖ ≤ ‖u‖ := by
  have hh := BoundedFieldOperator.multiply_norm (restrictionField s hs) u
  change ‖restriction s hs u‖ ≤ (1 : ℝ)*‖u‖ at hh
  simpa only [one_mul] using hh

/-- Bounded directions gain the square root of their actual spatial
support length when restricted to a cell. -/
theorem restriction_bounded (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s)
    (u : Space d) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) :
    ‖restriction s hs u‖ ≤ B*Real.sqrt ((μ).real s) := by
  let e := indicatorConstLp (E := ℝ) 2 hs (measure_ne_top μ s) 1
  have hb : ‖restriction s hs u‖ ≤ B*‖e‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [restriction_ae s hs u, hu,
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hr hx he
    change ‖restriction s hs u x‖ ≤ B*‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ) x‖
    rw [hr, he]
    by_cases hxs : x∈s <;> simp [hxs, hx, hB]
  have he : ‖e‖=Real.sqrt ((μ).real s) := by
    rw [norm_indicatorConstLp (by norm_num : (2 : ENNReal)≠0) (by norm_num : (2 : ENNReal)≠⊤)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, Real.sqrt_eq_rpow]
  rwa [he] at hb

/-- The exact Frobenius size of an interval mass is the norm of the
Hilbert-valued integral before the fixed matrix-coordinate conversion. -/
theorem mass_size (s : Set (AddCircle (1 : ℝ))) (u : Space d) :
    MatrixFrobeniusNorm.size (mass d s u)=‖∫ x in s, u x ∂μ‖ :=
  size_matrix _

end SHEStochastic.MatrixProfileNorms
