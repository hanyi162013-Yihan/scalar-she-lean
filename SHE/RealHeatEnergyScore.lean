module

public import SHE.RealHeatScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RealHeatEnergyScore
open Set MeasureTheory Real AddCircle HeatTorus HeatTorusKernel HeatProjection HeatChristoffel
  RealHeatScore GaussianGramScore GaussianIncrement
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- Real covariance score normalization retains any actual squared row scale,
including a clipped mass factor which vanishes. -/
theorem finite_real_heat_energy_score_bound (q : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i),
      (∀ i, t i ≤ h) →
      ∀ {D G : Type*} [AddCommGroup D] [Module ℝ D]
      [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
      (S : D →ₗ[ℝ] heatSpan t a) (C : D →ₗ[ℝ] G) [CompleteSpace C.range]
      (energy : D → ℝ) (c L : ℝ), 0 < c → 0 ≤ L →
      (∀ z, ‖S z‖ ^ 2 ≤ L ^ 2 * energy z) →
      (∀ z, c * energy z ≤ ‖C z‖ ^ 2) →
      ∀ x : UnitAddCircle, ∃ m ∈ C.range,
      (∀ z, inner ℝ (C z) m = realEvaluation t a ht x (S z)) ∧
      ‖m‖ ^ 2 ≤ (K * L ^ 2 / c) * ∑ i, GlobalTorusHeatSpan.weight (t i) (a i) x := by
  obtain ⟨h, K, hh, hh1, hK, hscore⟩ := finite_real_heat_score_bound q
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro t a ht hth D G _ _ _ _ _ S C _ energy c L hc hL hrow hcov x
  by_cases hL0 : L = 0
  · have hS (z : D) : S z = 0 := by
      have he := hrow z
      rw [hL0, zero_pow (by decide : 2 ≠ 0), zero_mul] at he
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (S z)])
    refine ⟨0, C.range.zero_mem, ?_, ?_⟩
    · intro z
      rw [hS, map_zero, inner_zero_right]
    · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), hL0, mul_zero, zero_mul, zero_div, le_refl]
  · have hL2 : 0 < L ^ 2 := sq_pos_of_ne_zero hL0
    have hdom (z : D) : (c / L ^ 2) * ‖S z‖ ^ 2 ≤ ‖C z‖ ^ 2 := by
      calc
        _ ≤ (c / L ^ 2) * (L ^ 2 * energy z) :=
          mul_le_mul_of_nonneg_left (hrow z) (by positivity)
        _ = c * energy z := by field_simp
        _ ≤ _ := hcov z
    obtain ⟨m, hm, hp, hn⟩ := hscore t a ht hth S C (c / L ^ 2) (by positivity) hdom x
    refine ⟨m, hm, hp, ?_⟩
    convert! hn using 1
    congr 1
    field_simp

variable {q n : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle) (ht : ∀ i, 0 < t i)

def evaluationFunctional (S : State n →ₗ[ℝ] heatSpan t a) (x : UnitAddCircle) : State n →L[ℝ] ℝ :=
  ((realEvaluation t a ht x).comp S).toContinuousLinearMap

def evaluationDirection (S : State n →ₗ[ℝ] heatSpan t a) (x : UnitAddCircle) : State n :=
  (InnerProductSpace.toDual ℝ (State n)).symm (evaluationFunctional t a ht S x)

/-- The physical finite observation direction is an actual Riesz vector,
uniquely determined by the real heat evaluation of every signed row. -/
theorem inner_evaluationDirection (S : State n →ₗ[ℝ] heatSpan t a) (x : UnitAddCircle) (z : State n) :
    inner ℝ z (evaluationDirection t a ht S x) = realEvaluation t a ht x (S z) := by
  rw [real_inner_comm]
  exact congrArg (fun L : State n →L[ℝ] ℝ => L z)
    ((InnerProductSpace.toDual ℝ (State n)).apply_symm_apply (evaluationFunctional t a ht S x))

theorem evaluationDirection_apply (S : State n →ₗ[ℝ] heatSpan t a) (x : UnitAddCircle) (i : Fin n) :
    evaluationDirection t a ht S x i = realEvaluation t a ht x (S (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  rw [← EuclideanSpace.basisFun_inner (Fin n) ℝ (evaluationDirection t a ht S x) i]
  exact inner_evaluationDirection t a ht S x _

end SHE.RealHeatEnergyScore
