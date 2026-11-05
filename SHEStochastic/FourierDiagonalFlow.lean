module

public import SHEStochastic.FourierCylinderGenerator
public import SHEStochastic.SmoothLinearFamily
public import SHEStochastic.ClampedAbsoluteContinuity
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.FourierDiagonalFlow
open SHE SHE.GaussianItoTest
open scoped ContDiff

variable {d : ℕ}

def axis (i : Fin d) : State d →L[ℝ] State d :=
  (EuclideanSpace.proj i).smulRight (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem norm_axis (i : Fin d) : ‖axis i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z i • EuclideanSpace.basisFun (Fin d) ℝ i‖ ≤ 1 * ‖z‖
  rw [norm_smul, (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one, mul_one, one_mul]
  exact PiLp.norm_apply_le z i

def raw (n : Fin d → ℤ) (t : ℝ) : State d →L[ℝ] State d :=
  ∑ i : Fin d, Real.exp (-t * (n i : ℝ) ^ 2) • axis i

theorem raw_apply (n : Fin d → ℤ) (t : ℝ) (z : State d) (j : Fin d) :
    raw n t z j = Real.exp (-t * (n j : ℝ) ^ 2) * z j := by
  change (EuclideanSpace.proj j) (raw n t z) = _
  simp only [raw, ContinuousLinearMap.sum_apply, map_sum, map_smul]
  simp [axis, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem raw_basis (n : Fin d → ℤ) (t : ℝ) (i : Fin d) :
    raw n t (EuclideanSpace.basisFun (Fin d) ℝ i) =
      Real.exp (-t * (n i : ℝ) ^ 2) • EuclideanSpace.basisFun (Fin d) ℝ i := by
  apply PiLp.ext
  intro j
  rw [raw_apply, PiLp.smul_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · have hz : EuclideanSpace.basisFun (Fin d) ℝ i j = 0 := by
      simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, hij]
    rw [hz, mul_zero, smul_zero]

theorem raw_zero (n : Fin d → ℤ) : raw n 0 = ContinuousLinearMap.id ℝ (State d) := by
  ext z i
  simp only [raw_apply, neg_zero, zero_mul, Real.exp_zero, one_mul, ContinuousLinearMap.id_apply]

theorem raw_inverse_scaled (n : Fin d → ℤ) (t : ℝ) (z : State d) :
    raw n t (WithLp.toLp 2 (fun i ↦ Real.exp (t * (n i : ℝ) ^ 2) * z i)) = z := by
  apply PiLp.ext
  intro i
  rw [raw_apply]
  change Real.exp (-t * (n i : ℝ) ^ 2) * (Real.exp (t * (n i : ℝ) ^ 2) * z i) = z i
  have he : Real.exp (-t * (n i : ℝ) ^ 2) * Real.exp (t * (n i : ℝ) ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [← mul_assoc, he, one_mul]

theorem norm_raw (n : Fin d → ℤ) {t : ℝ} (ht : 0 ≤ t) : ‖raw n t‖ ≤ d := by
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-t * (n i : ℝ) ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
      exact (mul_le_mul he (norm_axis i) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = _ := by simp

theorem contDiff_raw (n : Fin d → ℤ) : ContDiff ℝ ∞ (raw n) := by
  unfold raw
  fun_prop

def rawDerivative (n : Fin d → ℤ) (t : ℝ) : State d →L[ℝ] State d :=
  ∑ i : Fin d, (-(n i : ℝ) ^ 2 * Real.exp (-t * (n i : ℝ) ^ 2)) • axis i

theorem hasDerivAt_raw (n : Fin d → ℤ) (t : ℝ) : HasDerivAt (raw n) (rawDerivative n t) t := by
  unfold raw rawDerivative
  apply HasDerivAt.fun_sum
  intro i _
  convert (((hasDerivAt_id t).neg.mul_const ((n i : ℝ) ^ 2)).exp).smul_const (axis i) using 1 <;> simp <;> module

def clamped (H : ℝ) (n : Fin d → ℤ) (t : ℝ) : State d →L[ℝ] State d :=
  raw n (ClampedAbsoluteContinuity.clamp 0 H t)

theorem clamped_eq {H t : ℝ} (n : Fin d → ℤ) (ht : t ∈ Set.Icc 0 H) : clamped H n t = raw n t :=
  congrArg (raw n) (ClampedAbsoluteContinuity.of_mem ht)

theorem continuous_clamped (H : ℝ) (n : Fin d → ℤ) : Continuous (clamped H n) :=
  (contDiff_raw n).continuous.comp (ClampedAbsoluteContinuity.lipschitz 0 H).continuous

theorem norm_clamped (H : ℝ) (n : Fin d → ℤ) (t : ℝ) : ‖clamped H n t‖ ≤ d :=
  norm_raw n (le_max_left _ _)

/-- Existing uniform smooth calculus applies to the entire clamped
Fourier decay family with one finite-dimensional operator bound. -/
theorem uniformSmooth {F : State d → ℝ} (hF : SmoothCylinders.BoundedSmooth F) (H : ℝ) (n : Fin d → ℤ) :
    UniformSmooth.UniformBoundedSmooth (fun t z ↦ F (clamped H n t z)) :=
  SmoothLinearFamily.comp_family (UniformSmooth.UniformBoundedSmooth.fixed hF)
    (clamped H n) d (Nat.cast_nonneg _) (norm_clamped H n)

end SHEStochastic.FourierDiagonalFlow
