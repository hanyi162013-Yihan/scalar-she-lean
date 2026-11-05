module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ContinuousKernelLpAction
open MeasureTheory Filter
open scoped ENNReal

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] (ν : Measure X) [IsFiniteMeasure ν]

def value (g : Lp V 2 ν) (k : C(X, ℝ)) : Lp V 2 ν :=
  ((k.memLp ℝ (p := ∞) (μ := ν)).smul (Lp.memLp g)).toLp _

theorem value_ae (g : Lp V 2 ν) (k : C(X, ℝ)) :
    value ν g k =ᵐ[ν] fun x ↦ k x • g x :=
  ((k.memLp ℝ (p := ∞) (μ := ν)).smul (Lp.memLp g)).coeFn_toLp

theorem norm_bound (g : Lp V 2 ν) (k : C(X, ℝ)) : ‖value ν g k‖ ≤ ‖k‖ * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [value_ae ν g k] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg _)

/-- A fixed L2 coefficient acts continuously and linearly on the
continuous spatial kernel. It may be scalar, vector or matrix valued. -/
def operator (g : Lp V 2 ν) : C(X, ℝ) →L[ℝ] Lp V 2 ν :=
  LinearMap.mkContinuous
    { toFun := value ν g
      map_add' := fun k l ↦ by
        apply Lp.ext
        filter_upwards [value_ae ν g (k + l), value_ae ν g k, value_ae ν g l,
          Lp.coeFn_add (value ν g k) (value ν g l)] with x hkl hk hl hs
        rw [hkl, hs]
        simp only [ContinuousMap.add_apply, Pi.add_apply, hk, hl, add_smul]
      map_smul' := fun r k ↦ by
        apply Lp.ext
        filter_upwards [value_ae ν g (r • k), value_ae ν g k,
          Lp.coeFn_smul r (value ν g k)] with x hr hk hs
        simp only [RingHom.id_apply]
        rw [hr, hs]
        simp only [ContinuousMap.smul_apply, Pi.smul_apply, hk, smul_smul, smul_eq_mul] }
    ‖g‖ (fun k ↦ (norm_bound ν g k).trans_eq (mul_comm _ _))

theorem operator_ae (g : Lp V 2 ν) (k : C(X, ℝ)) :
    operator ν g k =ᵐ[ν] fun x ↦ k x • g x := value_ae ν g k

/-- Ordinary bounded-linear-map Fubini applies to the literal kernel
multiplied by an L2 coefficient, with no point evaluation on L2. -/
theorem integral_comm [CompleteSpace V] {A : Type*} [MeasurableSpace A]
    (η : Measure A) (g : Lp V 2 ν) (k : A → C(X, ℝ)) (hk : Integrable k η) :
    operator ν g (∫ a, k a ∂η) = ∫ a, operator ν g (k a) ∂η :=
  ((operator ν g).integral_comp_comm hk).symm

end SHEStochastic.ContinuousKernelLpAction
