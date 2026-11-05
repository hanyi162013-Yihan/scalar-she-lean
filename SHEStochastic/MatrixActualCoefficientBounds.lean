module

public import SHEStochastic.MatrixActualColumnCalculus
public import SHEStochastic.MatrixHaarZerothBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixActualCoefficientBounds
open Matrix MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixFrobeniusNorm
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (d : Type*) [Fintype d] (m U : ℝ) (n : ℕ) : ℝ :=
  max (MatrixHaarZerothBound.constant d m U) (MatrixHaarJetBounds.childConstant d m U n)

def weight (p : List Bool) (v : Domain (d := d)) : ℝ :=
  size (normalizedMass p false v)+size (normalizedMass p true v)

theorem weight_nonnegative (p : List Bool) (v : Domain (d := d)) : 0 ≤ weight p v :=
  add_nonneg (nonneg _) (nonneg _)

theorem constant_nonnegative (P : Profile d) (n : ℕ) : 0 ≤ constant d P.lower P.upper n :=
  (MatrixHaarZerothBound.nonnegative P.lower P.upper P.lower_pos P.upper_pos).trans (le_max_left _ _)

theorem normalized_cancel (p : List Bool) (b : Bool) (y : Domain (d := d)) :
    childLength p • normalizedMass p b y=mass (MatrixGlobalHaar.child p b) y := by
  change childLength p • ((childLength p)⁻¹ • mass (MatrixGlobalHaar.child p b) y)=_
  rw [smul_smul, mul_inv_cancel₀ (childLength_pos p).ne', one_smul]

theorem base (P : Profile d) (p : List Bool) :
    size (MatrixHaarAlgebra.left (mass (MatrixGlobalHaar.child p false) (MatrixProfileSymmetry.realize d P))
      (mass (MatrixGlobalHaar.child p true) (MatrixProfileSymmetry.realize d P))) ≤
        (Real.sqrt (childLength p))⁻¹*MatrixHaarZerothBound.constant d P.lower P.upper ∧
    size (MatrixHaarAlgebra.right (mass (MatrixGlobalHaar.child p false) (MatrixProfileSymmetry.realize d P))
      (mass (MatrixGlobalHaar.child p true) (MatrixProfileSymmetry.realize d P))) ≤
        (Real.sqrt (childLength p))⁻¹*MatrixHaarZerothBound.constant d P.lower P.upper := by
  let x := MatrixProfileSymmetry.realize d P
  let A := normalizedMass p false x
  let B := normalizedMass p true x
  have hp (b : Bool) : (normalizedMass p b x).PosDef := by
    rw [normalized_child]
    exact MatrixDyadicMass.average_positive P.value P.integrable P.lower P.lower_pos P.lower_bound _ _
  have hLo (b : Bool) : P.lower • (1 : Matrix d d ℝ) ≤ normalizedMass p b x := by
    rw [normalized_child]
    exact MatrixDyadicMass.average_lower P.value P.integrable P.lower P.lower_bound _ _
  have hHi (b : Bool) : normalizedMass p b x ≤ P.upper • (1 : Matrix d d ℝ) := by
    rw [normalized_child]
    exact MatrixDyadicMass.average_upper P.value P.integrable P.upper P.upper_bound _ _
  have hh := MatrixHaarZerothBound.children A B (hp false) (hp true) P.lower P.upper P.lower_pos P.upper_pos
    ⟨hLo false, hLo true⟩ ⟨hHi false, hHi true⟩
  have hc : 0 ≤ (Real.sqrt (childLength p))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  constructor
  · rw [← normalized_cancel p false x, ← normalized_cancel p true x,
      MatrixHaarScaling.left _ _ (hp false) (hp true) _ (childLength_pos p),
      MatrixFrobeniusNorm.smul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hh.1 hc
  · rw [← normalized_cancel p false x, ← normalized_cancel p true x,
      MatrixHaarScaling.right _ _ (hp false) (hp true) _ (childLength_pos p),
      MatrixFrobeniusNorm.smul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hh.2 hc

/-- A single uniform formula covers all actual coefficient orders,
including the undifferentiated coefficient in a first derivative term. -/
theorem all_orders (P : Profile d) (p : List Bool) (w : List (Domain (d := d))) :
    size (DirectionalJets.jet w (fun z => MatrixHaarAlgebra.left
      (mass (MatrixGlobalHaar.child p false) z) (mass (MatrixGlobalHaar.child p true) z))
      (MatrixProfileSymmetry.realize d P)) ≤
      (Real.sqrt (childLength p))⁻¹*(constant d P.lower P.upper w.length*MatrixJetClosure.weight (weight p) w) ∧
    size (DirectionalJets.jet w (fun z => MatrixHaarAlgebra.right
      (mass (MatrixGlobalHaar.child p false) z) (mass (MatrixGlobalHaar.child p true) z))
      (MatrixProfileSymmetry.realize d P)) ≤
      (Real.sqrt (childLength p))⁻¹*(constant d P.lower P.upper w.length*MatrixJetClosure.weight (weight p) w) := by
  have hc : 0 ≤ (Real.sqrt (childLength p))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  by_cases hw : w=[]
  · subst w
    have hh := base P p
    simp only [DirectionalJets.jet, List.length_nil, MatrixJetClosure.weight, List.map_nil, List.prod_nil, mul_one]
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc),
      hh.2.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc)⟩
  · have hh := coefficient_jets P p w hw
    have hB := mul_le_mul_of_nonneg_right
      (show MatrixHaarJetBounds.childConstant d P.lower P.upper w.length ≤ constant d P.lower P.upper w.length from le_max_right _ _)
      (MatrixJetClosure.weight_nonneg (weight p) (weight_nonnegative p) w)
    exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left hB hc), hh.2.trans (mul_le_mul_of_nonneg_left hB hc)⟩

end SHEStochastic.MatrixActualCoefficientBounds
