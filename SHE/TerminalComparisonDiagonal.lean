module
public import SHE.TerminalOrdinaryDiagonal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.TerminalComparisonDiagonal
open Filter Real
open scoped NNReal Topology

/-- All finite approximation slots share one arbitrary prescribed
tolerance. Upper frequencies are fixed first from the uniform heat
tail, and the companion index is chosen afterwards for that actual
finite ordinary-error budget. -/
theorem exists_index (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (κ M H ρ B K:ℝ)(Λ:ℕ→ℝ)(depth:ℕ→ℕ)(B0:ℕ→ℕ→ℝ≥0)(J:ℕ→ℕ)
    (δ:ℕ→ℝ)(hδ:∀k,0<δ k):
    ∃(m index:ℕ→ℕ),StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀k,0<m k ∧ SmoothReferenceLimit.error D (index k)<δ k ∧
        ∀E:ℝ,E≤(ScalarApproximationDiscrepancy.scalarError D (index k))^2*
          FullOrdinaryFiniteBandError.budget
            (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract)
            κ M H (Λ k) ρ B K D.beta (depth k) (B0 k)
            ((Finset.range (m k)).image (fun r=>J k+r))→
        sqrt E+ActualTerminalReconstructionEnergy.error D (index k) (J k) (m k)≤δ k:=by
  obtain ⟨m,hm⟩:=TerminalOrdinaryDiagonal.exists_lengths D.beta_pos
    (2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)) J
    (fun k=>δ k/4) (fun k=>div_pos (hδ k) (by norm_num))
  let C:ℕ→ℝ:=fun k=>FullOrdinaryFiniteBandError.budget
    (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract)
    κ M H (Λ k) ρ B K D.beta (depth k) (B0 k)
    ((Finset.range (m k)).image (fun r=>J k+r))
  obtain ⟨index,hi,hit,hbudget⟩:=FiniteOrdinaryErrorDiagonal.exists_index D C
    (fun k=>min ((δ k/4)^2) (δ k/4)) (fun k=>lt_min
      (sq_pos_of_pos (div_pos (hδ k) (by norm_num))) (div_pos (hδ k) (by norm_num)))
  refine ⟨m,index,hi,hit,fun k=>⟨(hm k).1,?_,?_⟩⟩
  · exact (hbudget k).2.trans_le ((min_le_right _ _).trans (by linarith only [hδ k]))
  · intro E hE
    have he:E≤(δ k/4)^2:=hE.trans ((mul_le_mul_of_nonneg_left
      (le_abs_self (C k)) (sq_nonneg (ScalarApproximationDiscrepancy.scalarError D (index k)))).trans
        ((hbudget k).1.le.trans (min_le_left _ _)))
    have hr:sqrt E≤δ k/4:=by
      have hq:0≤δ k/4:=(div_pos (hδ k) (by norm_num:(0:ℝ)<4)).le
      simpa only [sqrt_sq hq] using sqrt_le_sqrt he
    have hp:ScalarApproximationDiscrepancy.scalarError D (index k)≤δ k/4:=by
      have hp':SmoothReferenceLimit.error D (index k)≤δ k/4:=
        (hbudget k).2.le.trans (min_le_right _ _)
      have hs:=ScalarApproximationDiscrepancy.scalarError_nonneg D (index k)
      have hid:SmoothReferenceLimit.error D (index k)=
          2*ScalarApproximationDiscrepancy.scalarError D (index k):=by
        dsimp [SmoothReferenceLimit.error,ScalarApproximationDiscrepancy.scalarError]
        ring
      rw [hid] at hp'
      linarith only [hp',hs]
    have ht:=((hm k).2).le
    dsimp only [ActualTerminalReconstructionEnergy.error]
    linarith only [hr,hp,ht,hδ k]

end SHE.TerminalComparisonDiagonal
