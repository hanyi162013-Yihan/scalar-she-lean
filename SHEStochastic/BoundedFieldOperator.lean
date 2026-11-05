module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.BoundedFieldOperator

open MeasureTheory
open scoped NNReal

section General

variable {X E F G : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An essentially bounded measurable field of operators; its multiplication
operator acts on actual vector-valued `L²` functions. -/
structure Field (μ : Measure X) (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  value : X → E →L[ℝ] F
  measurable : AEStronglyMeasurable value μ
  bound : ℝ≥0
  norm_bound : ∀ᵐ x ∂μ, ‖value x‖ ≤ bound

theorem memLp (A : Field μ E F) (u : Lp E 2 μ) :
    MemLp (fun x => A.value x (u x)) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := (A.bound : ℝ))
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp_aestronglyMeasurable
      (A.measurable.prodMk (Lp.aestronglyMeasurable u)))
  filter_upwards [A.norm_bound] with x hx
  exact (A.value x).le_opNorm (u x) |>.trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def multiply (A : Field μ E F) (u : Lp E 2 μ) : Lp F 2 μ :=
  (memLp A u).toLp _

theorem multiply_ae (A : Field μ E F) (u : Lp E 2 μ) :
    ⇑(multiply A u) =ᵐ[μ] fun x => A.value x (u x) := (memLp A u).coeFn_toLp

def linear (A : Field μ E F) : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := multiply A
  map_add' u v := by
    apply Lp.ext
    filter_upwards [multiply_ae A (u + v), multiply_ae A u, multiply_ae A v,
      Lp.coeFn_add u v, Lp.coeFn_add (multiply A u) (multiply A v)] with x ha hu hv hb hc
    simp only [Pi.add_apply] at hb hc
    rw [ha, hc, hu, hv, hb, map_add]
  map_smul' r u := by
    apply Lp.ext
    filter_upwards [multiply_ae A (r • u), multiply_ae A u,
      Lp.coeFn_smul r u, Lp.coeFn_smul r (multiply A u)] with x ha hu hb hc
    simp only [RingHom.id_apply, Pi.smul_apply] at hb hc ⊢
    rw [ha, hc, hu, hb, map_smul]

theorem multiply_norm (A : Field μ E F) (u : Lp E 2 μ) :
    ‖multiply A u‖ ≤ (A.bound : ℝ) * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae A u, A.norm_bound] with x hx hb
  rw [hx]
  exact (A.value x).le_opNorm (u x) |>.trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

def operator (A : Field μ E F) : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (linear A).mkContinuous A.bound (multiply_norm A)

theorem operator_ae (A : Field μ E F) (u : Lp E 2 μ) :
    ⇑(operator A u) =ᵐ[μ] fun x => A.value x (u x) := multiply_ae A u

theorem operator_norm (A : Field μ E F) : ‖operator A‖ ≤ A.bound :=
  (operator A).opNorm_le_bound A.bound.coe_nonneg (multiply_norm A)

theorem operator_congr (A B : Field μ E F) (h : A.value =ᵐ[μ] B.value) :
    operator A = operator B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [operator_ae A u, operator_ae B u, h] with x ha hb hx
  rw [ha, hb, hx]

def comp (A : Field μ F G) (B : Field μ E F) : Field μ E G where
  value x := (A.value x).comp (B.value x)
  measurable := (ContinuousLinearMap.compL ℝ E F G).aestronglyMeasurable_comp₂
    A.measurable B.measurable
  bound := A.bound * B.bound
  norm_bound := by
    filter_upwards [A.norm_bound, B.norm_bound] with x ha hb
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul ha hb (norm_nonneg _) A.bound.coe_nonneg)

theorem operator_comp (A : Field μ F G) (B : Field μ E F) :
    operator (comp A B) = (operator A).comp (operator B) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [operator_ae (comp A B) u, operator_ae A (operator B u),
    operator_ae B u] with x hc ha hb
  change operator (comp A B) u x = operator A (operator B u) x
  rw [hc, ha, hb]
  rfl

def identity : Field μ E E where
  value _ := ContinuousLinearMap.id ℝ E
  measurable := aestronglyMeasurable_const
  bound := 1
  norm_bound := Filter.Eventually.of_forall fun _ => ContinuousLinearMap.norm_id_le

theorem operator_identity : operator (identity (μ := μ) (E := E)) =
    ContinuousLinearMap.id ℝ (Lp E 2 μ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [operator_ae (identity (μ := μ) (E := E)) u] with x hx
  exact hx

theorem operator_inverse (A : Field μ E F) (B : Field μ F E)
    (h : ∀ᵐ x ∂μ, (B.value x).comp (A.value x) = ContinuousLinearMap.id ℝ E) :
    (operator B).comp (operator A) = ContinuousLinearMap.id ℝ (Lp E 2 μ) := by
  rw [← operator_comp]
  exact (operator_congr (comp B A) identity h).trans operator_identity

def equivalence [CompleteSpace E] [CompleteSpace F] (A : Field μ E F) (B : Field μ F E)
    (hBA : ∀ᵐ x ∂μ, (B.value x).comp (A.value x) = ContinuousLinearMap.id ℝ E)
    (hAB : ∀ᵐ x ∂μ, (A.value x).comp (B.value x) = ContinuousLinearMap.id ℝ F) :
    Lp E 2 μ ≃L[ℝ] Lp F 2 μ := by
  have hleft : Function.LeftInverse (operator B) (operator A) := fun u =>
    congrArg (fun T : Lp E 2 μ →L[ℝ] Lp E 2 μ => T u) (operator_inverse A B hBA)
  have hright : Function.RightInverse (operator B) (operator A) := fun v =>
    congrArg (fun T : Lp F 2 μ →L[ℝ] Lp F 2 μ => T v) (operator_inverse B A hAB)
  exact ContinuousLinearEquiv.ofBijective (operator A)
    (LinearMap.ker_eq_bot.mpr hleft.injective) (LinearMap.range_eq_top.mpr hright.surjective)

end General

section Hilbert

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def adjoint (A : Field μ E F) : Field μ F E where
  value x := (A.value x).adjoint
  measurable := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.comp_aestronglyMeasurable A.measurable
  bound := A.bound
  norm_bound := by
    filter_upwards [A.norm_bound] with x hx
    exact (ContinuousLinearMap.adjoint.norm_map (A.value x)).le.trans hx

theorem operator_adjoint (A : Field μ E F) :
    operator (adjoint A) = (operator A).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae (adjoint A) u, operator_ae A v] with x ha hb
  rw [ha, hb]
  exact ContinuousLinearMap.adjoint_inner_left (A.value x) (v x) (u x)

end Hilbert
end SHEStochastic.BoundedFieldOperator
