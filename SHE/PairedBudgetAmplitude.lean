module

public import SHE.PairedRMSTimeBudget

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.PairedRMSTimeBudget
open Real GaussianAssignmentBlocks
open scoped NNReal BigOperators
variable {k:ℕ}

/-- The paired time budget is genuinely linear in the original root
amplitude. Its remaining constants are independent of that root. -/
theorem mass_amplitude (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (span χ A0 ν:ℝ) (i:Fin (k+1)):
    mass P ell C cs hc span χ A0 ν i=A0*mass P ell C cs hc span χ 1 ν i:=by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [mass,Fin.cases_zero,PhysicalAssignmentGapScale.prefactor]
    ring
  · simp only [mass,Fin.cases_succ,PairedPhysicalGapScale.prefactor]
    ring

theorem total_amplitude (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ)
    (k:ℕ) (span χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0):
    total P κ M ell C k span χ A0 ν order B0=
      A0*total P κ M ell C k span χ 1 ν order B0:=by
  unfold total
  dsimp only
  rw [mul_left_comm A0]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mass_amplitude P ell C _ _ span χ A0 ν i.2]
  ring

end SHE.PairedRMSTimeBudget
