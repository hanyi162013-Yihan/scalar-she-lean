module

public import SHEStochastic.MatrixRootCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixRootJets
open MeasureTheory MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixRootCalculus
open MatrixPhysicalColumnMap MatrixDirectionBounds
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem restriction_univ (u : MatrixProfileHilbert.Space d) : restriction Set.univ MeasurableSet.univ u = u := by
  apply Lp.ext
  filter_upwards [restriction_ae Set.univ MeasurableSet.univ u] with x hx
  simpa only [Set.indicator_univ] using hx

theorem norm_bounded (u : Domain (d := d)) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂μ, ‖u.val x‖ ≤ B) : ‖u‖ ≤ B := by
  have hh := MatrixProfileNorms.restriction_bounded Set.univ MeasurableSet.univ u.val B hB hu
  rw [restriction_univ] at hh
  convert! (by simpa [Measure.real] using hh : ‖u.val‖ ≤ B) using 1

theorem perturbation_norm (u : Domain (d := d)) : perturbation u ≤ ‖u‖ := by
  have hh := MatrixProfileCellBounds.mass_bound Set.univ MeasurableSet.univ u.val
  rw [restriction_univ] at hh
  have hh' : MatrixFrobeniusNorm.size (MatrixProfileHilbert.mass d Set.univ u.val) ≤ ‖u.val‖ := by
    simpa [Measure.real] using hh
  convert! hh' using 1

theorem global_root (P : Profile d) (i : d) :
    root i (MatrixProfileSymmetry.realize d P) = factor P (lp.single 2 (i, none) 1) := by
  rw [factor_single]
  apply Lp.ext
  filter_upwards [action_ae i (MatrixProfileHilbert.realize d P)
      (coefficient (MatrixProfileSymmetry.realize d P)),
    MatrixProfileHilbert.realize_ae d P,
    MatrixHaarRootColumns.constant_ae μ (MatrixFiniteHaar.inverseSqrt (∫ x, P.value x ∂μ)) i,
    BoundedFieldOperator.operator_ae (MatrixFieldOperator.field P.value P.measurable P.bound P.norm_bound)
      (MatrixHaarRootColumns.constant μ (MatrixFiniteHaar.inverseSqrt (∫ x, P.value x ∂μ)) i)]
      with x ha hp hc ho
  change action i (MatrixProfileHilbert.realize d P) (coefficient (MatrixProfileSymmetry.realize d P)) x =
    BoundedFieldOperator.operator (MatrixFieldOperator.field P.value P.measurable P.bound P.norm_bound)
      (MatrixHaarRootColumns.constant μ (MatrixFiniteHaar.inverseSqrt (∫ x, P.value x ∂μ)) i) x
  rw [ha, ho, hp, hc]
  rw [show MatrixProfileHilbert.toMatrix d (MatrixProfileHilbert.toVector d (P.value x)) = P.value x from
    (MatrixProfileHilbert.coordinates d).apply_symm_apply _]
  simp only [coefficient, total_realize]
  exact MatrixHaarRootColumns.column_mul _ _ i

theorem jets (P : Profile d) (i : d) (w : List (Domain (d := d))) :
    DirectionalJets.jet w (root i) (MatrixProfileSymmetry.realize d P) =
      action i (MatrixProfileSymmetry.realize d P).val
        (DirectionalJets.jet w coefficient (MatrixProfileSymmetry.realize d P)) +
      ((DirectionalJets.omissions w).map (fun q => action i q.1.val
        (DirectionalJets.jet q.2 coefficient (MatrixProfileSymmetry.realize d P)))).sum := by
  have hh := DirectionalJets.affine_bilinear (action i) 0 (MatrixProfileSymmetry.symmetric d).subtypeL
    (region P) (region_open P) (MatrixProfileSymmetry.realize d P) (region_self P) w coefficient (smooth P)
  simp only [zero_add] at hh
  convert! hh using 1

theorem bound (P : Profile d) (i : d) (w : List (Domain (d := d))) :
    ‖DirectionalJets.jet w (root i) (MatrixProfileSymmetry.realize d P)‖ ≤
      AffineOneInputBound.expression (constant d P.lower) perturbation (fun q : Domain (d := d) => ‖q.val‖)
        1 ‖(MatrixProfileSymmetry.realize d P).val‖ w := by
  rw [jets]
  apply (norm_add_le _ _).trans
  unfold AffineOneInputBound.expression
  simp only [inv_one, one_mul]
  apply add_le_add
  · exact (MatrixProfileNorms.action_bound _ _ _).trans
      (mul_le_mul_of_nonneg_right (coefficient_jets P w) (norm_nonneg _))
  · apply MatrixPhysicalJetBounds.norm_sum_map_le
    intro q hq
    exact (MatrixProfileNorms.action_bound _ _ _).trans
      (mul_le_mul_of_nonneg_right (coefficient_jets P q.2) (norm_nonneg _))

def orderConstant (P : Profile d) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * (profileBound P * constant d P.lower (k+1) +
    ((k : ℝ)+1) * constant d P.lower k)

theorem one_input (P : Profile d) (i : d) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ‖DirectionalJets.jet (v :: w) (root i) (MatrixProfileSymmetry.realize d P)‖ ≤
      orderConstant P w.length * ‖v‖ * MatrixJetClosure.weight B w := by
  have hA : 0 ≤ profileBound P := by
    have hU := P.upper_pos
    unfold profileBound
    positivity
  have ha : ‖(MatrixProfileSymmetry.realize d P).val‖ ≤ profileBound P * (1 : ℝ) := by
    have hh := norm_bounded (MatrixProfileSymmetry.realize d P) (profileBound P) hA (profile_bound P)
    convert! hh using 1 <;> simp
  have hh := AffineOneInputBound.one_input (constant d P.lower) (constant_nonnegative P)
    perturbation (fun q : Domain (d := d) => ‖q.val‖) B perturbation_nonnegative hB
    1 zero_lt_one ‖(MatrixProfileSymmetry.realize d P).val‖ (profileBound P) ‖v‖
    hA (norm_nonneg _) ha v (by rfl) (by simpa only [inv_one, one_mul] using perturbation_norm v) w (by
      intro q hq
      have hqB := norm_bounded q (B q) (hB q) (hRest q hq)
      constructor
      · exact (perturbation_norm q).trans (hqB.trans (by linarith [hB q]))
      · convert! hqB using 1 <;> simp)
  exact (bound P i (v :: w)).trans (by simpa only [inv_one, one_mul, orderConstant] using hh)

end SHEStochastic.MatrixRootJets
