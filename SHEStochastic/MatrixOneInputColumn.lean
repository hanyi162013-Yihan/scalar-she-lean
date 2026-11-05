module

public import SHEStochastic.MatrixDirectionBounds
public import SHEStochastic.AffineOneInputBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixOneInputColumn
open MeasureTheory MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixPhysicalJetBounds
open MatrixDirectionBounds
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- This constant depends only on dimension, ellipticity and order;
the profile enters only through its fixed lower/upper constants. -/
def orderConstant (P : Profile d) (k : ℕ) : ℝ :=
  (2 : ℝ)^k*(profileBound P*MatrixActualCoefficientBounds.constant d P.lower P.upper (k+1)+
    ((k : ℝ)+1)*MatrixActualCoefficientBounds.constant d P.lower P.upper k)

theorem branch (P : Profile d) (p : List Bool) (b : Bool) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q∈w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    branchBound P p b (v::w) ≤
      (Real.sqrt (childLength p))⁻¹*orderConstant P w.length*localSize p v*MatrixJetClosure.weight B w := by
  let C := MatrixActualCoefficientBounds.constant d P.lower P.upper
  let ρ : Domain (d := d) → ℝ := MatrixActualCoefficientBounds.weight p
  let R := fun q : Domain (d := d) =>
    ‖restricted (MatrixGlobalHaar.child p b) (MatrixGlobalHaar.child_measurable p b) q‖
  let a := R (MatrixProfileSymmetry.realize d P)
  let s := Real.sqrt (childLength p)
  have hs : 0 < s := Real.sqrt_pos.mpr (childLength_pos p)
  have hA : 0 ≤ profileBound P := by
    have hU := P.upper_pos
    unfold profileBound
    positivity
  have ha : a ≤ profileBound P*s :=
    restriction_bounded p b (MatrixProfileSymmetry.realize d P) (profileBound P) hA (profile_bound P)
  have hv : R v ≤ localSize p v := by
    cases b
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hh := AffineOneInputBound.one_input C (MatrixActualCoefficientBounds.constant_nonnegative P)
    ρ R B (MatrixActualCoefficientBounds.weight_nonnegative p) hB s hs a (profileBound P) (localSize p v)
    hA (localSize_nonneg p v) ha v hv (weight_one_input p v) w
    (fun q hq => ⟨weight_bounded p q (B q) (hB q) (hRest q hq),
      restriction_bounded p b q (B q) (hB q) (hRest q hq)⟩)
  have he : branchBound P p b (v::w)=AffineOneInputBound.expression C ρ R s a (v::w) := by
    simp only [branchBound, coefficientBound, AffineOneInputBound.expression]
    simp only [mul_assoc]
    rfl
  rw [← he] at hh
  exact hh

/-- Every actual matrix Haar detail derivative admits one arbitrary
localized Frobenius `L²` input; all remaining directions contribute
only their individual bounded norms. The derivative order, spatial
support and grid-independent constant are explicit. -/
theorem local_L2 (P : Profile d) (p : List Bool) (i : d) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q∈w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ‖DirectionalJets.jet (v::w) (fun z : Domain (d := d) =>
      MatrixPhysicalColumnMap.detail (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
        (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i z.val)
      (MatrixProfileSymmetry.realize d P)‖ ≤
      2*(Real.sqrt (childLength p))⁻¹*orderConstant P w.length*localSize p v*MatrixJetClosure.weight B w := by
  apply (detail_bound P p i (v::w)).trans
  apply (add_le_add (branch P p false v w B hB hRest) (branch P p true v w B hB hRest)).trans_eq
  ring

end SHEStochastic.MatrixOneInputColumn
