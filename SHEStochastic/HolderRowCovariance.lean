module

public import SHEStochastic.HolderStateRows
public import SHEStochastic.UnboundedCoefficientCutoff

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HolderRowCovariance
open MeasureTheory Filter
open scoped ENNReal NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

section Kernel
variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (ν : Measure X) [IsFiniteMeasure ν]

/-- Cross covariance of literal kernel-weighted L2 rows. Different
coefficient rows may come from different components of a matrix field. -/
theorem operator_inner (g h : Lp V 2 ν) (k l : C(X, ℝ)) :
    inner ℝ (ContinuousKernelLpAction.operator ν g k) (ContinuousKernelLpAction.operator ν h l) =
      ∫ x, k x * l x * inner ℝ (g x) (h x) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousKernelLpAction.operator_ae ν g k,
    ContinuousKernelLpAction.operator_ae ν h l] with x hk hl
  rw [hk, hl, real_inner_smul_left, real_inner_smul_right]
  ring

theorem operator_sub (g h : Lp V 2 ν) (k : C(X, ℝ)) :
    ContinuousKernelLpAction.operator ν g k - ContinuousKernelLpAction.operator ν h k =
      ContinuousKernelLpAction.operator ν (g - h) k := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (ContinuousKernelLpAction.operator ν g k) (ContinuousKernelLpAction.operator ν h k),
    ContinuousKernelLpAction.operator_ae ν g k, ContinuousKernelLpAction.operator_ae ν h k,
    ContinuousKernelLpAction.operator_ae ν (g - h) k, Lp.coeFn_sub g h] with x hs hg hh hd he
  rw [hs]
  change ContinuousKernelLpAction.operator ν g k x - ContinuousKernelLpAction.operator ν h k x = _
  rw [hg, hh, hd, he]
  exact (smul_sub _ _ _).symm

theorem continuous_coefficient (k : C(X, ℝ)) :
    Continuous (fun g : Lp V 2 ν ↦ ContinuousKernelLpAction.operator ν g k) := by
  apply (LipschitzWith.of_dist_le_mul (K := ‖k‖₊) (fun g h ↦ ?_)).continuous
  simp only [dist_eq_norm, coe_nnnorm, operator_sub]
  exact ContinuousKernelLpAction.norm_bound ν (g - h) k

end Kernel

section State
variable {P E V : Type*} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (U : P → Lp E 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) (hU : StronglyMeasurable U)
  {G K : E → V} {C D β : ℝ≥0} (hG : HolderWith C β G) (hK : HolderWith D β K)
  (hβ : 0 < β) (hβ1 : β ≤ 1)

/-- The actual predictable rows have the physical spatial covariance,
including cross covariances between different vector components. -/
theorem row_inner (k l : P → C(SHE.StoppedFourier.HeatCircle, ℝ)) (p : P) :
    inner ℝ (HolderStateRows.row U hU hG hβ hβ1 k p) (HolderStateRows.row U hU hK hβ hβ1 l p) =
      ∫ x, k p x * l p x * inner ℝ (G (U p x)) (K (U p x)) ∂AddCircle.haarAddCircle := by
  rw [HolderStateRows.row_operator, HolderStateRows.row_operator, operator_inner]
  apply integral_congr_ae
  filter_upwards [HolderCoefficientIntegrability.coefficient_ae hβ hβ1 hG (U p),
    HolderCoefficientIntegrability.coefficient_ae hβ hβ1 hK (U p)] with x hg hk
  rw [hg, hk]

theorem row_square (k l : P → C(SHE.StoppedFourier.HeatCircle, ℝ)) (p : P) :
    inner ℝ (HolderStateRows.row U hU hG hβ hβ1 k p) (HolderStateRows.row U hU hG hβ hβ1 l p) =
      ∫ x, k p x * l p x * ‖G (U p x)‖ ^ 2 ∂AddCircle.haarAddCircle := by
  simpa only [real_inner_self_eq_norm_sq] using row_inner U hU hG hG hβ hβ1 k l p

/-- Agreement of the physical coefficient values gives equality of the
actual Hilbert rows, independently of their chosen L2 representatives. -/
theorem row_congr (k : P → C(SHE.StoppedFourier.HeatCircle, ℝ)) (p : P)
    (hagree : ∀ᵐ x ∂AddCircle.haarAddCircle, G (U p x) = K (U p x)) :
    HolderStateRows.row U hU hG hβ hβ1 k p = HolderStateRows.row U hU hK hβ hβ1 k p := by
  apply Lp.ext
  filter_upwards [HolderStateRows.row_ae U hU hG hβ hβ1 k p,
    HolderStateRows.row_ae U hU hK hβ hβ1 k p, hagree] with x hg hk he
  rw [hg, hk, he]

end State
end SHEStochastic.HolderRowCovariance
