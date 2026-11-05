module

public import SHE.NativeHybridMoments
public import SHE.NoFreshOffsetCalculus
public import SHE.PairedOffsetCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.PairedTerminalConstants
open Real MeasureTheory
open scoped NNReal BigOperators
variable {k:ℕ}

/-- Pure finite-order constants: all ages, root clips, frequency powers
and current smallness remain OUTSIDE these constants. -/
def constant (P:CanonicalCovariance.ProfileParameters) (κ M:ℝ) (B:ℝ≥0)
    (choices:List (Fin k×Fin (k+1))) (χ:ℝ) (order:ℕ) (i:Fin (k+1)):ℝ:=
  let C0:=(k:ℝ)*(NativeHybridMoments.momentConstant (order*(k+2)) B κ M)^P.exponent
  Fin.cases (NoFreshAssignedMoments.constant P k k choices order C0)
    (fun j=>PairedRoughWordMoments.constant P choices j χ order (2*C0)) i

theorem constant_nonneg (P:CanonicalCovariance.ProfileParameters) {κ M:ℝ}
    (hκ:0≤κ) (hM:0≤M) (B:ℝ≥0) (choices:List (Fin k×Fin (k+1))) (χ:ℝ) (order:ℕ) (i:Fin (k+1)):
    0≤constant P κ M B choices χ order i:=by
  have hMC:0≤NativeHybridMoments.momentConstant (order*(k+2)) B κ M:=by
    unfold NativeHybridMoments.momentConstant
    exact mul_nonneg B.2 (pow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
  have hC:0≤(k:ℝ)*(NativeHybridMoments.momentConstant (order*(k+2)) B κ M)^P.exponent:=
    mul_nonneg (Nat.cast_nonneg _) (rpow_nonneg hMC _)
  refine Fin.cases ?_ (fun j=>?_) i
  · exact NoFreshAssignedMoments.constant_nonneg P order choices hC
  · exact PairedRoughWordMoments.constant_nonneg P choices j χ order (mul_nonneg (by norm_num) hC)

end SHE.PairedTerminalConstants
