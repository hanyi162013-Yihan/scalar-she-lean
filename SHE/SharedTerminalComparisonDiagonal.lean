module
public import SHE.TerminalComparisonDiagonal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.SharedTerminalComparisonDiagonal
open Filter Real
open scoped Topology

/-- Finitely many original probability spaces use the SAME smooth
companion index. Their numerical finite-prefix budgets may differ and
grow arbitrarily with the chosen upper frequency. No convergence of
the canonical smooth laws or of the companion paths is assumed. -/
theorem exists_index {ι:Type*}[Fintype ι](D:SmoothApproximation.ScalarData)
    (C:ι→ℕ→ℕ→ℝ)(J:ℕ→ℕ)(δ:ℕ→ℝ)(hδ:∀k,0<δ k):
    ∃(m index:ℕ→ℕ),StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀k,0<m k ∧ SmoothReferenceLimit.error D (index k)<δ k ∧
        ∀(i:ι)(E:ℝ),E≤(ScalarApproximationDiscrepancy.scalarError D (index k))^2*C i k (m k)→
          sqrt E+ActualTerminalReconstructionEnergy.error D (index k) (J k) (m k)≤δ k:=by
  classical
  obtain ⟨m,hm⟩:=TerminalOrdinaryDiagonal.exists_lengths D.beta_pos
    (2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)) J
    (fun k=>δ k/4) (fun k=>div_pos (hδ k) (by norm_num))
  let Ct:ℕ→ℝ:=fun k=>∑i:ι,|C i k (m k)|
  have hCt(k:ℕ):0≤Ct k:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hCi(i:ι)(k:ℕ):C i k (m k)≤|Ct k|:=by
    have hh:|C i k (m k)|≤Ct k:=Finset.single_le_sum
      (fun j _=>abs_nonneg (C j k (m k))) (Finset.mem_univ i)
    exact (le_abs_self _).trans (hh.trans (le_abs_self _))
  obtain ⟨index,hi,hit,hbudget⟩:=FiniteOrdinaryErrorDiagonal.exists_index D Ct
    (fun k=>min ((δ k/4)^2) (δ k/4)) (fun k=>lt_min
      (sq_pos_of_pos (div_pos (hδ k) (by norm_num))) (div_pos (hδ k) (by norm_num)))
  refine ⟨m,index,hi,hit,fun k=>⟨(hm k).1,?_,?_⟩⟩
  · exact (hbudget k).2.trans_le ((min_le_right _ _).trans (by linarith only [hδ k]))
  · intro i E hE
    have he:E≤(δ k/4)^2:=hE.trans ((mul_le_mul_of_nonneg_left
      (hCi i k) (sq_nonneg (ScalarApproximationDiscrepancy.scalarError D (index k)))).trans
        ((hbudget k).1.le.trans (min_le_left _ _)))
    have hq:0≤δ k/4:=(div_pos (hδ k) (by norm_num:(0:ℝ)<4)).le
    have hr:sqrt E≤δ k/4:=by simpa only [sqrt_sq hq] using sqrt_le_sqrt he
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

end SHE.SharedTerminalComparisonDiagonal
