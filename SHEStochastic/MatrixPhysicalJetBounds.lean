module

public import SHEStochastic.MatrixActualCoefficientBounds
public import SHEStochastic.MatrixProfileCellBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixPhysicalJetBounds
open MeasureTheory MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

def coefficient (p : List Bool) (b : Bool) (z : Domain (d := d)) : Matrix d d ℝ :=
  if b then MatrixHaarAlgebra.right (mass (MatrixGlobalHaar.child p false) z) (mass (MatrixGlobalHaar.child p true) z)
  else MatrixHaarAlgebra.left (mass (MatrixGlobalHaar.child p false) z) (mass (MatrixGlobalHaar.child p true) z)

def coefficientBound (P : Profile d) (p : List Bool) (w : List (Domain (d := d))) : ℝ :=
  (Real.sqrt (childLength p))⁻¹*(MatrixActualCoefficientBounds.constant d P.lower P.upper w.length*
    MatrixJetClosure.weight (MatrixActualCoefficientBounds.weight p) w)

theorem coefficient_bound (P : Profile d) (p : List Bool) (b : Bool) (w : List (Domain (d := d))) :
    MatrixFrobeniusNorm.size (DirectionalJets.jet w (coefficient p b) (MatrixProfileSymmetry.realize d P)) ≤
      coefficientBound P p w := by
  cases b
  · exact (MatrixActualCoefficientBounds.all_orders P p w).1
  · exact (MatrixActualCoefficientBounds.all_orders P p w).2

def branchJet (P : Profile d) (p : List Bool) (i : d) (b : Bool) (w : List (Domain (d := d))) :
    Physical (d := d) :=
  MatrixPhysicalColumnMap.action i
    (restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) (MatrixProfileSymmetry.realize d P))
    (DirectionalJets.jet w (coefficient p b) (MatrixProfileSymmetry.realize d P))+
  ((DirectionalJets.omissions w).map (fun q => MatrixPhysicalColumnMap.action i
    (restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) q.1)
    (DirectionalJets.jet q.2 (coefficient p b) (MatrixProfileSymmetry.realize d P)))).sum

def branchBound (P : Profile d) (p : List Bool) (b : Bool) (w : List (Domain (d := d))) : ℝ :=
  coefficientBound P p w*
    ‖restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) (MatrixProfileSymmetry.realize d P)‖+
  ((DirectionalJets.omissions w).map (fun q => coefficientBound P p q.2*
    ‖restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) q.1‖)).sum

theorem norm_sum_map_le {X F : Type*} [NormedAddCommGroup F]
    (l : List X) (f : X → F) (B : X → ℝ) (h : ∀ x∈l, ‖f x‖ ≤ B x) :
    ‖(l.map f).sum‖ ≤ (l.map B).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy))))

theorem branch_bound (P : Profile d) (p : List Bool) (i : d) (b : Bool) (w : List (Domain (d := d))) :
    ‖branchJet P p i b w‖ ≤ branchBound P p b w := by
  unfold branchJet branchBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (MatrixProfileNorms.action_bound _ _ _).trans
      (mul_le_mul_of_nonneg_right (coefficient_bound P p b w) (norm_nonneg _))
  · apply norm_sum_map_le
    intro q hq
    exact (MatrixProfileNorms.action_bound _ _ _).trans
      (mul_le_mul_of_nonneg_right (coefficient_bound P p b q.2) (norm_nonneg _))

/-- An actual all-order physical-column `L²` estimate, retaining the
localized profile norms and normalized interval-mass weights needed
for the one-input and signed transport estimates. -/
theorem detail_bound (P : Profile d) (p : List Bool) (i : d) (w : List (Domain (d := d))) :
    ‖DirectionalJets.jet w (fun z : Domain (d := d) =>
      MatrixPhysicalColumnMap.detail (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
        (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i z.val)
      (MatrixProfileSymmetry.realize d P)‖ ≤ branchBound P p false w+branchBound P p true w := by
  have hm := mul_pos (childLength_pos p) P.lower_pos
  have he := detail_jets (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
    (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i
    (MatrixProfileSymmetry.realize d P) (childLength p*P.lower) hm
    (child_positive P p false) (child_positive P p true) ⟨child_lower P p false, child_lower P p true⟩ w
  change DirectionalJets.jet w _ _=branchJet P p i false w+branchJet P p i true w at he
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (branch_bound P p i false w) (branch_bound P p i true w))

end SHEStochastic.MatrixPhysicalJetBounds
