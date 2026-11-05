module
public import SHE.FullOrdinaryFiniteDiagonal
public import SHE.ActualTerminalReconstructionEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.TerminalOrdinaryDiagonal
open Filter Real
open scoped NNReal Topology

/-- The upper-frequency prefix is fixed using only the uniform Holder
tail, before the companion index is chosen. Every prefix has positive length. -/
theorem exists_lengths {β:ℝ}(hβ:0<β)(A:ℝ)(J:ℕ→ℕ)(δ:ℕ→ℝ)(hδ:∀k,0<δ k):
    ∃m:ℕ→ℕ,∀k,0<m k ∧ A*CompactMollifier.radius (J k+m k)^β<δ k:=by
  have ht:Tendsto (fun l:ℕ=>A*CompactMollifier.radius l^β) atTop (𝓝 (0:ℝ)):=by
    simpa only [zero_rpow hβ.ne',mul_zero] using
      (CompactMollifier.radius_tendsto.rpow_const (Or.inr hβ.le)).const_mul A
  have he(k:ℕ):∃l:ℕ,∀r≥l,A*CompactMollifier.radius r^β<δ k:=
    eventually_atTop.mp (ht.eventually (gt_mem_nhds (hδ k)))
  choose l hl using he
  refine ⟨fun k=>l k+1,fun k=>⟨Nat.succ_pos _,?_⟩⟩
  exact hl k (J k+(l k+1)) (by omega)

/-- One honest diagonal controls the true terminal reconstruction and
the full actual finite-frequency ordinary-error budget. Frequency
lengths are chosen first; the same strictly increasing smooth index
then meets every fixed numerical budget. No infinite ordinary-error
series or convergence of the companion paths is used. -/
theorem exists_index (D:SmoothApproximation.ScalarData){tau:ℝ}(htau:0<tau)(htau1:tau≤1)
    (hcontract:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*tau^(D.beta/4)≤1/2)
    (κ M H ρ B K:ℝ)(Λ:ℕ→ℝ)(hΛ:∀k,0<Λ k)
    (depth:ℕ→ℕ)(B0:ℕ→ℕ→ℝ≥0)(J:ℕ→ℕ):
    ∃(m index:ℕ→ℕ),StrictMono index ∧ Tendsto index atTop atTop ∧
      ∀k,0<m k ∧
        2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)*
          CompactMollifier.radius (J k+m k)^D.beta<(Λ k)^(-2:ℝ) ∧
        (ScalarApproximationDiscrepancy.scalarError D (index k))^2*
          |FullOrdinaryFiniteBandError.budget
            (ControlledSmoothLimit.roughTotalParameters D htau htau1 hcontract)
            κ M H (Λ k) ρ B K D.beta (depth k) (B0 k)
            ((Finset.range (m k)).image (fun r=>J k+r))|<(Λ k)^(-4:ℝ) ∧
        SmoothReferenceLimit.error D (index k)<(Λ k)^(-4:ℝ):=by
  obtain ⟨m,hm⟩:=exists_lengths D.beta_pos
    (2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)) J
    (fun k=>(Λ k)^(-2:ℝ)) (fun k=>rpow_pos_of_pos (hΛ k) _)
  obtain ⟨index,hi,hit,hbudget⟩:=FullOrdinaryFiniteDiagonal.exists_index D htau htau1 hcontract
    κ M H ρ B K Λ hΛ depth B0 (fun k=>(Finset.range (m k)).image (fun r=>J k+r))
  exact ⟨m,index,hi,hit,fun k=>⟨(hm k).1,(hm k).2,(hbudget k).1,(hbudget k).2⟩⟩

end SHE.TerminalOrdinaryDiagonal
