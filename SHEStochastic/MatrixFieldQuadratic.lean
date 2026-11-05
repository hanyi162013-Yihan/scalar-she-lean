module

public import SHEStochastic.MatrixFieldOperator
public import SHEStochastic.MatrixEllipticSize

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFieldQuadratic
open MeasureTheory Matrix
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

variable {d X : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace X]
  {μ : Measure X}

theorem lower (A : Matrix d d ℝ) (m : ℝ) (hLo : m • (1 : Matrix d d ℝ) ≤ A)
    (v : EuclideanSpace ℝ d) :
    m*‖v‖^2 ≤ inner ℝ v (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A v) := by
  have hh := MatrixEllipticSize.quadratic A m hLo v.ofLp
  rw [Matrix.inner_toEuclideanCLM, EuclideanSpace.real_norm_sq_eq]
  exact hh

theorem upper (A : Matrix d d ℝ) (U : ℝ) (hHi : A ≤ U • (1 : Matrix d d ℝ))
    (v : EuclideanSpace ℝ d) :
    inner ℝ v (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A v) ≤ U*‖v‖^2 := by
  have hp : (U • (1 : Matrix d d ℝ)-A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hHi)
  have hh := hp.dotProduct_mulVec_nonneg v.ofLp
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hh
  rw [Matrix.inner_toEuclideanCLM, EuclideanSpace.real_norm_sq_eq]
  have he : v.ofLp ⬝ᵥ v.ofLp=∑ i, (v i)^2 := by simp only [dotProduct, pow_two]
  rw [he] at hh
  linarith

/-- Uniform pointwise ellipticity gives the actual vector spatial
`L²` coercivity estimate, with the same lower constant. -/
theorem operator_lower (κ : X → Matrix d d ℝ) (hκ : Measurable κ)
    (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (m : ℝ)
    (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (u : Lp (EuclideanSpace ℝ d) 2 μ) :
    m*‖u‖^2 ≤ inner ℝ u (MatrixFieldOperator.operator κ hκ B hB u) := by
  have hn := L2.integrable_inner (𝕜 := ℝ) u u
  simp only [real_inner_self_eq_norm_sq] at hn
  have he : (∫ x, ‖u x‖^2 ∂μ)=‖u‖^2 := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) u u).symm
  rw [L2.inner_def, ← he, ← integral_const_mul]
  apply integral_mono_ae (hn.const_mul m) (L2.integrable_inner (𝕜 := ℝ) _ _)
  filter_upwards [hLo, BoundedFieldOperator.operator_ae (MatrixFieldOperator.field κ hκ B hB) u] with x hx hop
  change m*‖u x‖^2 ≤ inner ℝ (u x)
    (BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hB) u x)
  rw [hop]
  exact lower (κ x) m hx (u x)

theorem operator_upper (κ : X → Matrix d d ℝ) (hκ : Measurable κ)
    (B : ℝ≥0) (hB : ∀ᵐ x ∂μ, ‖κ x‖ ≤ B) (U : ℝ)
    (hHi : ∀ᵐ x ∂μ, κ x ≤ U • (1 : Matrix d d ℝ))
    (u : Lp (EuclideanSpace ℝ d) 2 μ) :
    inner ℝ u (MatrixFieldOperator.operator κ hκ B hB u) ≤ U*‖u‖^2 := by
  have hn := L2.integrable_inner (𝕜 := ℝ) u u
  simp only [real_inner_self_eq_norm_sq] at hn
  have he : (∫ x, ‖u x‖^2 ∂μ)=‖u‖^2 := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.inner_def (𝕜 := ℝ) u u).symm
  rw [L2.inner_def, ← he, ← integral_const_mul]
  apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) _ _) (hn.const_mul U)
  filter_upwards [hHi, BoundedFieldOperator.operator_ae (MatrixFieldOperator.field κ hκ B hB) u] with x hx hop
  change inner ℝ (u x)
    (BoundedFieldOperator.operator (MatrixFieldOperator.field κ hκ B hB) u x) ≤ U*‖u x‖^2
  rw [hop]
  exact upper (κ x) U hx (u x)

end SHEStochastic.MatrixFieldQuadratic
