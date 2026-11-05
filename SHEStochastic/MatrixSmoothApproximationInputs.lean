module

public import SHEStochastic.MatrixSmoothApproximation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixSmoothApproximationInputs
open MeasureTheory Filter SHE MatrixNonlinearCoefficient MatrixSmoothApproximation
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator Topology
variable {n : ℕ} (G : Coefficient (Fin n)) {K β : ℝ}

def error (K β : ℝ) (m : ℕ) : ℝ := MatrixSmoothCoefficient.sqrtConstant G*
  ((2*(G.bound : ℝ)*K)*CompactMollifier.radius m^(β/2)*GaussianNormMoment.moment (Fin n) β)

theorem error_nonneg (hK : 0 ≤ K) (β : ℝ) (m : ℕ) : 0 ≤ error G K β m := by
  unfold error
  exact mul_nonneg (MatrixSmoothCoefficient.sqrtConstant_nonneg G)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)
      (Real.rpow_nonneg (CompactMollifier.radius_pos m).le _)) (GaussianNormMoment.nonneg _))

theorem error_tendsto (K : ℝ) (hβ : 0 < β) : Tendsto (error G K β) atTop (𝓝 0) := by
  have he := ((CompactMollifier.radius_tendsto.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ β/2))).const_mul
    (2*(G.bound : ℝ)*K)).mul_const (GaussianNormMoment.moment (Fin n) β)
  unfold error
  simpa only [Real.zero_rpow (by positivity : β/2 ≠ 0),mul_zero,zero_mul] using
    he.const_mul (MatrixSmoothCoefficient.sqrtConstant G)

/-- The zero-scale coefficient is exactly the canonical positive root. -/
theorem zero_value (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w,‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (z : EuclideanSpace ℝ (Fin n)) :
    (MatrixSmoothCoefficient.coefficient G 0).value z=CFC.sqrt (G.covariance z) := by
  have hh := MatrixSmoothCoefficient.error G (ε := 0) (by norm_num) hK hβ.le hG z
  simp only [Real.zero_rpow (by positivity : β/2 ≠ 0),mul_zero,zero_mul] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem close (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w,‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (m : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖(MatrixSmoothCoefficient.coefficient G 0).value z-(coefficient G m).value z‖ ≤ error G K β m := by
  rw [zero_value G hK hβ hG,norm_sub_rev]
  exact MatrixSmoothCoefficient.error G (CompactMollifier.radius_pos m).le hK hβ.le hG z

theorem covariance_eq (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w,‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (z : EuclideanSpace ℝ (Fin n)) :
    (MatrixSmoothCoefficient.coefficient G 0).covariance z=G.covariance z := by
  change (MatrixSmoothCoefficient.coefficient G 0).value z*
    star ((MatrixSmoothCoefficient.coefficient G 0).value z)=_
  rw [zero_value G hK hβ hG,(CFC.sqrt_nonneg (G.covariance z)).star_eq]
  exact CFC.sqrt_mul_sqrt_self (G.covariance z)
    ((smul_nonneg G.lower_pos.le zero_le_one).trans (G.lower_bound z))

/-- Bundle a proved norm Holder estimate in mathlib's metric interface. -/
theorem holder_of_norm {E V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup V]
    {f : E → V} (C β : ℝ≥0) (h : ∀ x y,‖f x-f y‖ ≤ (C : ℝ)*‖x-y‖^(β : ℝ)) : HolderWith C β f := by
  intro x y
  have hh := ENNReal.ofReal_le_ofReal (h x y)
  simpa only [edist_dist,dist_eq_norm,ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) β.coe_nonneg] using hh

theorem holder_family (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w,‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) (ε : ℝ) :
    HolderWith ⟨holderConstant G K,holderConstant_nonneg G hK⟩ ⟨β,hβ⟩
      (MatrixSmoothCoefficient.coefficient G ε).value :=
  holder_of_norm _ _ (MatrixSmoothCoefficient.holder G hG ε)

end SHEStochastic.MatrixSmoothApproximationInputs
