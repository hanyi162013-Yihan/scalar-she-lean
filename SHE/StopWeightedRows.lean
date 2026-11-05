module

public import SHE.FiniteHeatRows
public import SHE.MixedNativeJointPhysical

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.StopWeightedRows
open Set MeasureTheory Real StoppedFourier WordRecursion FiniteHeatRows
open scoped ENNReal NNReal BigOperators
local instance stopWeightedRows_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def diagonal (e : Fin n → ℝ) : State n →L[ℝ] State n :=
  Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.diagonal e)

theorem diagonal_apply (e : Fin n → ℝ) (z : State n) (i : Fin n) :
    diagonal e z i=e i*z i := by
  change (WithLp.ofLp (Matrix.toEuclideanCLM (𝕜:=ℝ) (Matrix.diagonal e) z)) i=_
  simp only [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec_diagonal]

theorem diagonal_norm_le (e : Fin n → ℝ) (he : ∀ i,|e i| ≤ 1) (z : State n) :
    ‖diagonal e z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonal_apply,mul_pow]
  have hi : (e i)^2 ≤ 1 := by nlinarith [sq_abs (e i),sq_nonneg (e i),he i,abs_nonneg (e i)]
  exact (mul_le_mul_of_nonneg_right hi (sq_nonneg (z i))).trans_eq (one_mul _)

theorem diagonal_basis (e : Fin n → ℝ) (i : Fin n) :
    diagonal e (EuclideanSpace.basisFun (Fin n) ℝ i)=
      e i • EuclideanSpace.basisFun (Fin n) ℝ i := by
  apply PiLp.ext
  intro j
  rw [diagonal_apply]
  by_cases hij : i=j
  · subst j
    simp
  · simp [EuclideanSpace.basisFun_apply,hij,Ne.symm hij]

theorem coefficient_diagonal (D : State n →L[ℝ] ℝ) (e : Fin n → ℝ) (i : Fin n) :
    coefficient (D.comp (diagonal e)) i=coefficient D i*e i := by
  simp only [coefficient,ContinuousLinearMap.comp_apply,diagonal_basis,map_smul,smul_eq_mul]
  exact mul_comm _ _

def weights (Λ : ℝ) (Z : Fin n → Observation) (q : ℝ) (i : Fin n) : ℝ :=
  exp (-Λ*((Z i).stop-q))

theorem weights_pos (Λ : ℝ) (Z : Fin n → Observation) (q : ℝ) (i : Fin n) :
    0 < weights Λ Z q i := exp_pos _

theorem weights_le_one {Λ : ℝ} (hΛ : 0 ≤ Λ) (Z : Fin n → Observation) (q : ℝ)
    (hq : ∀ i,q ≤ (Z i).stop) (i : Fin n) : weights Λ Z q i ≤ 1 := by
  apply exp_le_one_iff.mpr
  simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hΛ (sub_nonneg.mpr (hq i)))

def weightedHeatRow (Λ : ℝ) (Z : Fin n → Observation) (q r : ℝ) (y : HeatCircle) : State n :=
  diagonal (weights Λ Z q) (heatRow Z r y)

def kernel (D : State n →L[ℝ] ℝ) (Λ : ℝ) (Z : Fin n → Observation) (q r : ℝ) : CircleL2 :=
  FiniteHeatRows.kernel (D.comp (diagonal (weights Λ Z q))) Z r

theorem kernel_eq_sum (D : State n →L[ℝ] ℝ) (Λ : ℝ) (Z : Fin n → Observation) (q r : ℝ) :
    kernel D Λ Z q r=∑ i : Fin n,((coefficient D i*weights Λ Z q i:ℝ):ℂ) •
      circleHeat ((Z i).target-r) (Z i).center := by
  simp only [kernel,FiniteHeatRows.kernel,coefficient_diagonal]

theorem kernel_ae (D : State n →L[ℝ] ℝ) (Λ : ℝ) (Z : Fin n → Observation)
    (q r : ℝ) (hr : ∀ i,r < (Z i).target) :
    (kernel D Λ Z q r : HeatCircle → ℂ)=ᵐ[AddCircle.haarAddCircle]
      fun y => ((D (weightedHeatRow Λ Z q r y):ℝ):ℂ) :=
  FiniteHeatRows.kernel_ae (D.comp (diagonal (weights Λ Z q))) Z hr

/-- The correct signed-noise row splits at a later heat time while its
stop weights, Gaussian law and current mean all stay at q. -/
theorem functional_split (D : State n →L[ℝ] ℝ) (Λ : ℝ) (Z : Fin n → Observation)
    {q r : ℝ} (hqr : q ≤ r) (hr : ∀ i,r < (Z i).target) :
    FiniteHeatRows.functional (D.comp (diagonal (weights Λ Z q))) Z q=
      (FiniteHeatRows.functional (D.comp (diagonal (weights Λ Z q))) Z r).comp
        (circleHeatOperator (r-q) (sub_nonneg.mpr hqr)) :=
  FiniteHeatRows.functional_split _ Z hqr hr

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def combination (D : State n →L[ℝ] ℝ) (v : Fin n → E) : E :=
  ∑ i : Fin n,coefficient D i • v i

/-- Exact derivative-row decomposition. The signed difference is paired
with diag(e), not with the unweighted heat row. -/
theorem combination_interpolate (D : State n →L[ℝ] ℝ) (e : Fin n → ℝ) (u v : Fin n → E) :
    combination D (fun i => v i+(1-e i) • (u i-v i))=
      combination D u+combination (D.comp (diagonal e)) (fun i => v i-u i) := by
  simp only [combination,coefficient_diagonal,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  module

end Algebra

end SHE.StopWeightedRows
