module

public import SHE.ScalarRange
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RealGramInverse
open Set MeasureTheory Matrix
open scoped InnerProductSpace

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def coefficients (v : I → G) (d : G) : I → ℝ :=
  (Matrix.gram ℝ v)⁻¹ *ᵥ (fun i => inner ℝ (v i) d)

def projection (v : I → G) (d : G) : G := ∑ i, coefficients v d i • v i

theorem coefficients_add (v : I → G) (d e : G) :
    coefficients v (d + e) = coefficients v d + coefficients v e := by
  have heq : (fun i => inner ℝ (v i) (d + e)) =
      (fun i => inner ℝ (v i) d) + (fun i => inner ℝ (v i) e) := by
    funext i
    exact inner_add_right _ _ _
  rw [coefficients, heq, Matrix.mulVec_add]
  rfl

theorem coefficients_smul (v : I → G) (b : ℝ) (d : G) :
    coefficients v (b • d) = b • coefficients v d := by
  have heq : (fun i => inner ℝ (v i) (b • d)) = b • (fun i => inner ℝ (v i) d) := by
    funext i
    simp only [inner_smul_right, Pi.smul_apply, smul_eq_mul]
  rw [coefficients, heq, Matrix.mulVec_smul]
  rfl

theorem coefficients_linearCombination (v : I → G) (hv : LinearIndependent ℝ v) (b : I → ℝ) :
    coefficients v (∑ i, b i • v i) = b := by
  have hdet : IsUnit (Matrix.gram ℝ v).det := isUnit_iff_ne_zero.mpr
    (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)
  have heq : (fun i => inner ℝ (v i) (∑ j, b j • v j)) = (Matrix.gram ℝ v) *ᵥ b := by
    funext i
    simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, Matrix.gram_apply]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [coefficients, heq, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem projection_eq_self (v : I → G) (hv : LinearIndependent ℝ v) {d : G}
    (hd : d ∈ Submodule.span ℝ (Set.range v)) : projection v d = d := by
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hd
  rw [← hb, projection, coefficients_linearCombination v hv]

theorem measurable_inverse_entries {X : Type*} [MeasurableSpace X]
    (A : X → Matrix I I ℝ) (hA : Measurable A) (i j : I) :
    Measurable (fun x => (A x)⁻¹ i j) := by
  have hd : Measurable (fun x => (A x).det) := continuous_id.matrix_det.measurable.comp hA
  have ha : Measurable (fun x => (A x).adjugate) := continuous_id.matrix_adjugate.measurable.comp hA
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  exact hd.inv.mul ha.eval_matrix

/-- Every fixed Gram-inverse coefficient branch is Borel, including its
conventional values on singular matrices. -/
theorem coefficients_measurable {X : Type*} [MeasurableSpace X]
    (v : X → I → G) (d : X → G)
    (hv : ∀ i, StronglyMeasurable (fun x => v x i)) (hd : StronglyMeasurable d) (i : I) :
    Measurable (fun x => coefficients (v x) (d x) i) := by
  have hA : Measurable (fun x => Matrix.gram ℝ (v x)) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact ((hv i).inner (hv j)).measurable
  unfold coefficients Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro j _
  exact (measurable_inverse_entries _ hA i j).mul (((hv j).inner hd).measurable)

end SHE.RealGramInverse
