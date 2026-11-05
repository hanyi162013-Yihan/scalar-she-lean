module

public import SHE.PairedTerminalConstants
public import SHE.PairedSourceBudget
public import SHE.OrderedHeatForests
public import SHE.ParentHeatForests

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.PairedRMSWeights
open MeasureTheory Real OrderedHeatForests
open scoped NNReal

/-- Frequency enters only the paired ROOT source coefficient. A paired
ROUGH source keeps its own coefficient, avoiding a second frequency loss. -/
def coefficient {k:ℕ} (P:CanonicalCovariance.ProfileParameters) (κ M:ℝ)
    (B0:ℝ≥0) (cs:List (Fin k×Fin (k+1))) (χ ν:ℝ) (order:ℕ) (i:Fin (k+1)):ℝ:=
  2*(PairedTerminalConstants.constant P κ M B0 cs χ order i)^(1/(order:ℝ))*
    PairedSourceBudget.coefficient P.holder P.exponent χ (Fin.cases ν (fun _=>0) i)*
      (Fintype.card (Choices 1 k):ℝ)^2

theorem coefficient_nonneg {k:ℕ} (P:CanonicalCovariance.ProfileParameters) {κ M:ℝ}
    (hκ:0≤κ) (hM:0≤M) (B0:ℝ≥0) (cs:List (Fin k×Fin (k+1))) (χ ν:ℝ) (order:ℕ) (i:Fin (k+1)):
    0≤coefficient P κ M B0 cs χ ν order i:=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (rpow_nonneg (PairedTerminalConstants.constant_nonneg P hκ hM B0 cs χ order i) _))
    (PairedSourceBudget.coefficient_nonneg P.holder_nonneg)) (sq_nonneg _)

end SHE.PairedRMSWeights
