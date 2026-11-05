module
public import SHE.MixedPastNewestApproximation
public import SHE.ScalarApproximationDiagonal
public import SHE.HilbertFiniteEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.FiniteOrdinaryErrorDiagonal
open Filter
open scoped Topology

/-- Finite frequency/depth budgets may grow arbitrarily with damping.
One deterministic strictly increasing companion index controls BOTH the
actual ordinary insertion error and the actual coefficient-root error.
No uniform bound in the retained finite frequency cutoff is assumed. -/
theorem exists_index(D:SmoothApproximation.ScalarData)(C δ:ℕ→ℝ)(hδ:∀k,0<δ k):
    ∃index:ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀k,(ScalarApproximationDiscrepancy.scalarError D (index k))^2*|C k|<δ k ∧
        SmoothReferenceLimit.error D (index k)<δ k:=by
  let err:Fin 2→ℕ→ℝ→ℝ:=fun i n _=>if i=0 then
    (ScalarApproximationDiscrepancy.scalarError D n)^2 else SmoothReferenceLimit.error D n
  have ht(i:Fin 2):Tendsto (fun n=>err i n 0) atTop (𝓝 (0:ℝ)):=by
    fin_cases i
    · simpa [err] using
        (MixedPastNewestApproximation.scalarError_tendsto D).pow 2
    · simpa [err] using SmoothReferenceLimit.error_tendsto D
  obtain ⟨index,hi,hit,herr⟩:=SHE.common_approximation_diagonal_tendsto
    (Finset.univ:Finset (Fin 2)) err (fun _=>0) (fun k=>δ k/(|C k|+1))
    (fun k=>div_pos (hδ k) (by positivity)) (fun _ i _=>ht i)
  refine ⟨index,hi,hit,fun k=>?_⟩
  have h0:(ScalarApproximationDiscrepancy.scalarError D (index k))^2<δ k/(|C k|+1):=by
    simpa only [err,ite_true,abs_of_nonneg (sq_nonneg (ScalarApproximationDiscrepancy.scalarError D (index k)))] using herr k 0 (Finset.mem_univ _)
  have h1:SmoothReferenceLimit.error D (index k)<δ k/(|C k|+1):=by
    simpa only [err,show (1:Fin 2)≠0 by decide,ite_false,
      abs_of_nonneg (SmoothReferenceLimit.error_nonneg D (index k))] using herr k 1 (Finset.mem_univ _)
  have hmul:(ScalarApproximationDiscrepancy.scalarError D (index k))^2*(|C k|+1)<δ k:=
    (lt_div_iff₀ (by positivity : (0:ℝ) < |C k| + 1)).mp h0
  have hratio:δ k/(|C k|+1)≤δ k:=by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < |C k| + 1)).mpr
    nlinarith [mul_nonneg (hδ k).le (abs_nonneg (C k))]
  exact ⟨(by nlinarith [sq_nonneg (ScalarApproximationDiscrepancy.scalarError D (index k))]),h1.trans_le hratio⟩
end SHE.FiniteOrdinaryErrorDiagonal
