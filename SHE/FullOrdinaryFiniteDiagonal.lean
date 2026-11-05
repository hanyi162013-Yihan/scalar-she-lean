module
public import SHE.FullOrdinaryFiniteBandError
public import SHE.FiniteOrdinaryErrorDiagonal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.FullOrdinaryFiniteDiagonal
open Filter Real
open scoped NNReal Topology

/-- One deterministic companion index controls the ACTUAL full-time,
finite-frequency ordinary-error budget and the root approximation error.
All retained band sets/depths may vary with damping before this index is
chosen. No companion-process convergence is required. -/
theorem exists_index (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (κ M H ρ B K:ℝ)(Λ:ℕ→ℝ)(hΛ:∀k,0<Λ k)
    (depth:ℕ→ℕ)(B0:ℕ→ℕ→ℝ≥0)(s:ℕ→Finset ℕ):
    ∃index:ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀k,(ScalarApproximationDiscrepancy.scalarError D (index k))^2*
        |FullOrdinaryFiniteBandError.budget
          (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract)
          κ M H (Λ k) ρ B K D.beta (depth k) (B0 k) (s k)|<(Λ k)^(-4:ℝ) ∧
        SmoothReferenceLimit.error D (index k)<(Λ k)^(-4:ℝ):=by
  exact FiniteOrdinaryErrorDiagonal.exists_index D
    (fun k=>FullOrdinaryFiniteBandError.budget
      (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract)
      κ M H (Λ k) ρ B K D.beta (depth k) (B0 k) (s k))
    (fun k=>(Λ k)^(-4:ℝ)) (fun k=>rpow_pos_of_pos (hΛ k) _)

/-- Applying the selected numerical budget to the actual squared
ordinary-error energy gives precisely the vanishing RMS slot used in
the finite master inequality. -/
theorem rms_le {Λ E err C:ℝ}(hΛ:0<Λ)(hE:E≤err^2*C)
    (hsmall:err^2*|C|<Λ^(-4:ℝ)):
    sqrt E≤Λ^(-2:ℝ):=by
  have hE':E<Λ^(-4:ℝ):=(hE.trans
    (mul_le_mul_of_nonneg_left (le_abs_self C) (sq_nonneg err))).trans_lt hsmall
  have hs:=sqrt_le_sqrt hE'.le
  have he:sqrt (Λ^(-4:ℝ))=Λ^(-2:ℝ):=by
    rw [sqrt_eq_rpow,←rpow_mul hΛ.le]
    congr 1
    norm_num
  simpa only [he] using hs
end SHE.FullOrdinaryFiniteDiagonal
