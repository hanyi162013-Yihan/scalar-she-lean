module

public import SHEStochastic.MatrixProfileEntries
public import SHEStochastic.MatrixPhysicalJetStructure
public import SHEStochastic.MatrixPhysicalJetBounds
public import SHEStochastic.AffineOneInputBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixTransformedJets
open MeasureTheory MatrixInfiniteHaar MatrixProfileEntries MatrixPhysicalColumnSmooth
open MatrixPhysicalJetBounds MatrixActualColumnCalculus MatrixPhysicalJetStructure
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d E : Type*} [Fintype d] [DecidableEq d] [NormedAddCommGroup E] [NormedSpace ℝ E]

def localSize (p : List Bool) (b : Bool) (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E)
    (u : Domain (d := d)) : ℝ :=
  transformedSize T (restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) u)

def expression (P : Profile d) (p : List Bool) (b : Bool) (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E)
    (w : List (Domain (d := d))) : ℝ :=
  AffineOneInputBound.expression (MatrixActualCoefficientBounds.constant d P.lower P.upper)
    (MatrixActualCoefficientBounds.weight p) (localSize p b T)
    (Real.sqrt (childLength p)) (localSize p b T (MatrixProfileSymmetry.realize d P)) w

def profileConstant (P : Profile d) (A : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * (A * MatrixActualCoefficientBounds.constant d P.lower P.upper (k+1) +
    ((k : ℝ)+1) * MatrixActualCoefficientBounds.constant d P.lower P.upper k)

theorem profileConstant_nonneg (P : Profile d) (A : ℝ) (hA : 0 ≤ A) (k : ℕ) :
    0 ≤ profileConstant P A k := by
  have h1 := MatrixActualCoefficientBounds.constant_nonnegative P (k+1)
  have h0 := MatrixActualCoefficientBounds.constant_nonnegative P k
  unfold profileConstant
  positivity

theorem one_input (P : Profile d) (p : List Bool) (b : Bool)
    (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q) (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (ha : localSize p b T (MatrixProfileSymmetry.realize d P) ≤ A * Real.sqrt (childLength p))
    (hv : localSize p b T v ≤ β)
    (hm : MatrixActualCoefficientBounds.weight p v ≤ (Real.sqrt (childLength p))⁻¹ * β)
    (hw : ∀ q ∈ w, MatrixActualCoefficientBounds.weight p q ≤ 2 * B q ∧
      localSize p b T q ≤ B q * Real.sqrt (childLength p)) :
    expression P p b T (v :: w) ≤
      (Real.sqrt (childLength p))⁻¹ * profileConstant P A w.length * β * MatrixJetClosure.weight B w :=
  AffineOneInputBound.one_input _ (MatrixActualCoefficientBounds.constant_nonnegative P)
    _ _ _ (MatrixActualCoefficientBounds.weight_nonnegative p) hB
    _ (Real.sqrt_pos.mpr (childLength_pos p)) _ _ _ hA hβ ha v hv hm w hw

theorem branch_bound (P : Profile d) (p : List Bool) (b : Bool) (i r : d)
    (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E) (w : List (Domain (d := d))) :
    ‖T (component r (branchJet P p i b w))‖ ≤ expression P p b T w := by
  let L := T.comp (component r)
  change ‖L (branchJet P p i b w)‖ ≤ _
  simp only [branchJet, map_add, map_list_sum, List.map_map, Function.comp_def]
  unfold expression AffineOneInputBound.expression
  apply (norm_add_le _ _).trans
  apply add_le_add
  · have hc := coefficient_bound P p b w
    unfold coefficientBound at hc
    rw [← mul_assoc] at hc
    exact (transformed_action T _ i r _).trans
      (mul_le_mul_of_nonneg_right hc (transformedSize_nonneg T _))
  · apply norm_sum_map_le
    intro q hq
    have hc := coefficient_bound P p b q.2
    unfold coefficientBound at hc
    rw [← mul_assoc] at hc
    exact (transformed_action T _ i r _).trans
      (mul_le_mul_of_nonneg_right hc (transformedSize_nonneg T _))

/-- A scalar spatial output transform can be moved through every
actual matrix Haar derivative. Its only physical norms occur on the
two affine numerator slots, allowing direct reuse of scalar negative
and Gaussian row estimates. -/
theorem bound (P : Profile d) (p : List Bool) (i r : d)
    (T : SHE.DyadicApproximation.RealL2 →L[ℝ] E) (w : List (Domain (d := d))) :
    ‖T (component r (jetColumn P p i w))‖ ≤ expression P p false T w + expression P p true T w := by
  have hm := mul_pos (childLength_pos p) P.lower_pos
  have he := detail_jets (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
    (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i
    (MatrixProfileSymmetry.realize d P) (childLength p*P.lower) hm
    (child_positive P p false) (child_positive P p true) ⟨child_lower P p false, child_lower P p true⟩ w
  change jetColumn P p i w = branchJet P p i false w + branchJet P p i true w at he
  rw [he, map_add, map_add]
  exact (norm_add_le _ _).trans (add_le_add (branch_bound P p false i r T w) (branch_bound P p true i r T w))

end SHEStochastic.MatrixTransformedJets
