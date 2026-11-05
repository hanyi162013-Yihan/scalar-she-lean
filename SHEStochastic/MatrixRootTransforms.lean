module

public import SHEStochastic.MatrixRootJets
public import SHEStochastic.MatrixProfileEntries
public import SHEStochastic.MatrixNegativeJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixRootTransforms
open MeasureTheory MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixRootCalculus MatrixProfileEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d E : Type*} [Fintype d] [DecidableEq d] [NormedAddCommGroup E] [NormedSpace ℝ E]

def expression (P : Profile d) (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E)
    (w : List (Domain (d := d))) : ℝ :=
  AffineOneInputBound.expression (constant d P.lower) perturbation
    (fun q : Domain (d := d) => transformedSize T q.val) 1
    (transformedSize T (MatrixProfileSymmetry.realize d P).val) w

def profileConstant (P : Profile d) (A : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * (A * constant d P.lower (k+1) + ((k : ℝ)+1) * constant d P.lower k)

theorem profileConstant_nonneg (P : Profile d) (A : ℝ) (hA : 0 ≤ A) (k : ℕ) :
    0 ≤ profileConstant P A k := by
  have h1 := constant_nonnegative P (k+1)
  have h0 := constant_nonnegative P k
  unfold profileConstant
  positivity

theorem bound (P : Profile d) (i r : d) (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E)
    (w : List (Domain (d := d))) :
    ‖T (component r (DirectionalJets.jet w (root i) (MatrixProfileSymmetry.realize d P)))‖ ≤
      expression P T w := by
  let L := T.comp (component r)
  change ‖L (DirectionalJets.jet w (root i) (MatrixProfileSymmetry.realize d P))‖ ≤ _
  rw [MatrixRootJets.jets]
  simp only [map_add, map_list_sum, List.map_map, Function.comp_def]
  unfold expression AffineOneInputBound.expression
  simp only [inv_one, one_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (transformed_action T _ i r _).trans
      (mul_le_mul_of_nonneg_right (coefficient_jets P w) (transformedSize_nonneg T _))
  · apply MatrixPhysicalJetBounds.norm_sum_map_le
    intro q hq
    exact (transformed_action T _ i r _).trans
      (mul_le_mul_of_nonneg_right (coefficient_jets P q.2) (transformedSize_nonneg T _))

theorem one_input (P : Profile d) (i r : d) (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E)
    (v : Domain (d := d)) (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ)
    (hB : ∀ q, 0 ≤ B q) (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (ha : transformedSize T (MatrixProfileSymmetry.realize d P).val ≤ A)
    (hv : transformedSize T v.val ≤ β) (hm : perturbation v ≤ β)
    (hw : ∀ q ∈ w, perturbation q ≤ 2 * B q ∧ transformedSize T q.val ≤ B q) :
    ‖T (component r (DirectionalJets.jet (v :: w) (root i) (MatrixProfileSymmetry.realize d P)))‖ ≤
      profileConstant P A w.length * β * MatrixJetClosure.weight B w := by
  have hh := AffineOneInputBound.one_input (constant d P.lower) (constant_nonnegative P)
    perturbation (fun q : Domain (d := d) => transformedSize T q.val) B perturbation_nonnegative hB
    1 zero_lt_one _ A β hA hβ (by simpa using ha) v hv (by simpa using hm) w (by simpa using hw)
  apply (bound P i r T (v :: w)).trans
  convert! hh using 1 <;> simp only [expression, inv_one, one_mul, profileConstant]

end SHEStochastic.MatrixRootTransforms
