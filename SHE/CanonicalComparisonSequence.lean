module
public import SHE.CommonComparisonCutoff
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.CanonicalComparisonSequence
open Real Filter Topology
open scoped NNReal
/-- A concrete diverging damping sequence and common cutoffs are chosen
before any companion index or original probability space. -/
theorem exists_sequence(D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
    (H:ℝ≥0)(hH:0<H)(N:ℕ):
    ∃(Λ:ℕ→ℝ)(J:ℕ→ℕ),(∀k,1≤Λ k) ∧ Tendsto Λ atTop atTop ∧
      (∀k,(Λ k)^(1/4:ℝ)≤(2:ℝ)^(J k+1)) ∧
      (∀k,(2:ℝ)^(J k)≤2*(Λ k)^(1/4:ℝ)) ∧
      ∀k,CommonComparisonCutoff.Ready D.ell D.cap D.ell_pos D.cap_nonneg
        (SHE.rho D.beta) (by dsimp [SHE.rho];linarith [D.beta_le])
        (by dsimp [SHE.rho];linarith [D.beta_pos])
        D hT hT1 hsmall H hH (N+1) (J k):=by
  have hr:0<SHE.rho D.beta:=by dsimp [SHE.rho];linarith [D.beta_le]
  have hrh:SHE.rho D.beta<1/2:=by dsimp [SHE.rho];linarith [D.beta_pos]
  obtain ⟨B,hB,hcut⟩:=CommonComparisonCutoff.exists_threshold D.ell D.cap D.ell_pos D.cap_nonneg
    (SHE.rho D.beta) hr hrh D hT hT1 hsmall H hH (N+1)
  let Λ:ℕ→ℝ:=fun k=>(k:ℝ)+(B+1)
  have hLB(k:ℕ):B≤Λ k:=by have hk:0≤(k:ℝ):=Nat.cast_nonneg k;dsimp only [Λ];linarith
  have hL(k:ℕ):1≤Λ k:=by have hk:0≤(k:ℝ):=Nat.cast_nonneg k;dsimp only [Λ];linarith
  have ht:Tendsto Λ atTop atTop:=tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  choose J hJ using (fun k=>hcut (Λ k) (hLB k))
  exact ⟨Λ,J,hL,ht,fun k=>(hJ k).2.2.1.le,fun k=>(hJ k).2.1,fun k=>(hJ k).2.2.2.2⟩
end SHE.CanonicalComparisonSequence
