module

public import SHE.PairedRMSWeights
public import SHE.TerminalRootTimeIntegral
public import SHE.TerminalPairedGapIntegrals

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.PairedRMSTimeBudget
open Real GaussianAssignmentBlocks PhysicalAssignmentGapScale
open scoped NNReal BigOperators

def mass {k:ℕ} (P:CanonicalCovariance.ProfileParameters) (ell:ℝ) (C:ℕ→ℝ)
    (cs:List (Fin k×Fin (k+1))) (hc:cs∈assignments (m:=k+1) (List.finRange k))
    (span χ A0 ν:ℝ) (i:Fin (k+1)):ℝ:=
  Fin.cases
    (2*scorePrefactor ell C k*prefactor P cs A0 1*
      (((k+1:ℕ):ℝ)^2*AllocatedAssignmentKernel.inverseDegreeProduct cs hc (P.exponent/4))*
        span^((k:ℝ)*P.exponent/4)*
          rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span^(AllocatedAssignmentKernel.rootCount cs))
    (fun j=>scorePrefactor ell C k*PairedPhysicalGapScale.prefactor P cs j χ A0*
      (((k+1:ℕ):ℝ)^2*HeterogeneousAssignmentKernel.inverseDegreeProduct cs hc
        (HeterogeneousAssignmentKernel.pairedDegree P.exponent χ j))*
        span^((k:ℝ)*P.exponent/4-χ/4)*
          rootMass (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) span^(AllocatedAssignmentKernel.rootCount cs)) i

/-- An explicit FINITE all-order terminal remainder time budget. Every
original root clip and every root/rough assignment remains in the sum. -/
def total (P:CanonicalCovariance.ProfileParameters) (κ M ell:ℝ) (C:ℕ→ℝ) (k:ℕ)
    (span χ A0 ν:ℝ) (order:ℕ) (B0:ℝ≥0):ℝ:=
  let cs:=assignments (m:=k+1) (List.finRange k)
  (1/2:ℝ)^k*sqrt ((cs.length*(k+1):ℕ):ℝ)*
    ∑i:Fin cs.length×Fin (k+1),
      sqrt (PairedRMSWeights.coefficient P κ M B0 (cs.get i.1) χ ν order i.2)*
        mass P ell C (cs.get i.1) (List.get_mem cs i.1) span χ A0 ν i.2

end SHE.PairedRMSTimeBudget
