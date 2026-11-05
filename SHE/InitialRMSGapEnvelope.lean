module

public import SHE.InitialAssignmentEnvelope
public import SHE.MixedPastTerminalRMS

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.InitialRMSGapEnvelope
open Set MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators NNReal

/-- The full positive original-gap kernel for the initial triangle.
This is the SAME finite assignment sum as the actual RMS amplitude. -/
def kernel (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ) (k:ℕ)
    (h χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0) (d:Fin k→ℝ):ℝ:=
  let cs:=assignments (m:=k+1) (List.finRange k)
  (1/2:ℝ)^k*sqrt ((cs.length*(k+1):ℕ):ℝ)*
    ∑i:Fin cs.length×Fin (k+1),sqrt (PairedRMSWeights.coefficient P κ M B0 (cs.get i.1) χ ν order i.2)*
      InitialAssignmentEnvelope.kernel P ell C (cs.get i.1) h χ A0 ν i.2 d

theorem kernel_measurable (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ) (k:ℕ)
    (h χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0):Measurable (kernel P κ M ell C k h χ A0 ν order B0):=by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact (InitialAssignmentEnvelope.kernel_measurable P ell C _ h χ A0 ν i.2).const_mul _

theorem kernel_nonneg (P:CanonicalCovariance.ProfileParameters) {κ M ell h χ A0 ν:ℝ}
    (hell:0<ell) (C:ℕ→ℝ) (hC:∀j,0≤C j) (k:ℕ) (hh:0≤h) (hA0:0≤A0) (hν:0≤ν)
    (order:ℕ) (B0:ℝ≥0) (d:Fin k→ℝ):0≤kernel P κ M ell C k h χ A0 ν order B0 d:=by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sqrt_nonneg _) (InitialAssignmentEnvelope.kernel_nonneg P hell C hC _ hh hA0 hν i.2 d)

/-- Exact original finite RMS budget controls the initial envelope mass;
there is no initial strip loss or extra rough-leaf degree. -/
theorem kernel_integral (P:CanonicalCovariance.ProfileParameters) {κ M ell h χ A0 ν:ℝ}
    (hell:0<ell) (C:ℕ→ℝ) (hC:∀j,0≤C j) (k:ℕ) (hh:0<h) (hχ:0≤χ) (hχβ:χ<P.exponent)
    (hA0:0≤A0) (hν:0≤ν) (order:ℕ) (B0:ℝ≥0):
    Integrable (kernel P κ M ell C k h χ A0 ν order B0) ∧
      (∫d,kernel P κ M ell C k h χ A0 ν order B0 d)≤
        PairedRMSTimeBudget.total P κ M ell C k h χ A0 ν order B0:=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  have hi(i:Fin cs.length×Fin (k+1)):=InitialAssignmentEnvelope.kernel_integral P hell C hC
    (cs.get i.1) (List.get_mem cs i.1) hh hχ hχβ hA0 hν i.2
  refine ⟨?_,?_⟩
  · apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _=>(hi i).1.const_mul _)
  · unfold kernel PairedRMSTimeBudget.total
    rw [integral_const_mul,integral_finsetSum _ (fun i _=>(hi i).1.const_mul _)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hi i).2 (sqrt_nonneg _)

end SHE.InitialRMSGapEnvelope
