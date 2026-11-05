module

public import SHE.HaarRiesz
public import SHE.CircleSquareRoot

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar

open MeasureTheory AddCircle CircleHeat
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem factor_inverse_norm_bound (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (x : HaarInput) :
    ‖x‖ ≤ (Real.sqrt m)⁻¹ * ‖factor f m U hm hfreal hfbound x‖ := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hb : Real.sqrt m * ‖x‖ ≤ ‖factor f m U hm hfreal hfbound x‖ := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hm.le]
    exact factor_norm_sq_lower f m U hm hfreal hfbound x
  have hh : ‖x‖ ≤ ‖factor f m U hm hfreal hfbound x‖ / Real.sqrt m :=
    (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- The actual countable weighted-Haar factor is a bounded linear
equivalence, with covariance and Riesz lower bound proved from its columns. -/
def factorEquivalence (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) : HaarInput ≃L[ℂ] CircleL2 :=
  SynthesisEquivalence.equivalence (factor f m U hm hfreal hfbound)
    (CircleMultiplier.equivalence f m U hm (hfbound.mono (fun _ h => h.1))
      (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound))
    (factor_covariance f m U hm hfreal hfbound) (Real.sqrt m)⁻¹
    (factor_inverse_norm_bound f m U hm hfreal hfbound)

@[simp] theorem factorEquivalence_apply (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (x : HaarInput) :
    factorEquivalence f m U hm hfreal hfbound x = factor f m U hm hfreal hfbound x := rfl

theorem factorEquivalence_inverse_bound (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    ‖(factorEquivalence f m U hm hfreal hfbound).symm v‖ ≤ (Real.sqrt m)⁻¹ * ‖v‖ := by
  have hh := factor_inverse_norm_bound f m U hm hfreal hfbound
    ((factorEquivalence f m U hm hfreal hfbound).symm v)
  change _ ≤ (Real.sqrt m)⁻¹ *
    ‖factorEquivalence f m U hm hfreal hfbound ((factorEquivalence f m U hm hfreal hfbound).symm v)‖ at hh
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh

/-- The actual manuscript innovation rotation `J(c)=L(c)⁻¹ M_(sqrt c)`.
It is a genuine unitary map from physical noise to the common Haar input. -/
def innovationRotation (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) : CircleL2 ≃ₗᵢ[ℂ] HaarInput :=
  SynthesisEquivalence.comparison (factorEquivalence f m U hm hfreal hfbound)
    (CircleMultiplier.rootEquivalence f m U hm (hfbound.mono (fun _ h => h.1))
      (hfbound.mono (fun _ h => h.2))) (by
        change (factor f m U hm hfreal hfbound).comp (factor f m U hm hfreal hfbound).adjoint = _
        rw [factor_covariance]
        exact (CircleMultiplier.rootEquivalence_covariance f m U hm hfreal
          (hfbound.mono (fun _ h => h.1)) (hfbound.mono (fun _ h => h.2))
          (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound)).symm)

@[simp] theorem innovationRotation_apply (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    innovationRotation f m U hm hfreal hfbound v =
      (factorEquivalence f m U hm hfreal hfbound).symm
        (CircleMultiplier.rootEquivalence f m U hm (hfbound.mono (fun _ h => h.1))
          (hfbound.mono (fun _ h => h.2)) v) := rfl

theorem innovationRotation_norm (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    ‖innovationRotation f m U hm hfreal hfbound v‖ = ‖v‖ :=
  (innovationRotation f m U hm hfreal hfbound).norm_map v

theorem factor_innovationRotation (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    factor f m U hm hfreal hfbound (innovationRotation f m U hm hfreal hfbound v) =
      CircleMultiplier.rootEquivalence f m U hm (hfbound.mono (fun _ h => h.1))
        (hfbound.mono (fun _ h => h.2)) v := by
  rw [innovationRotation_apply]
  exact (factorEquivalence f m U hm hfreal hfbound).apply_symm_apply _

end SHE.FiniteHaar
