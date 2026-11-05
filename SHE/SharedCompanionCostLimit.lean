module
public import SHE.SharedTerminalComparisonDiagonal
public import SHE.SequentialReferenceMasterCost
public import SHE.NativeHigherMasterFiniteCoefficient
public import SHE.NativeMasterRHSCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.SharedCompanionCostLimit
open Filter Topology Real

/-- A single structural constant can dominate both the actual master
constant and the independently proved true-energy bridge constant. -/
theorem bound_mono {β C₀ C Λ K m err a b:ℝ}
    (hΛ:0≤Λ)(hK:0≤K)(hm:0≤m)(ha:0≤a)(hb:0≤b)(hC:C₀≤C)
    (h:ActualReferenceMasterClosure.Bound β C₀ Λ K m err a b 0 0):
    ActualReferenceMasterClosure.Bound β C Λ K m err a b 0 0:=by
  have hs:0≤a*K+b*m+ActualReferenceMasterClosure.rows β Λ m 0 0:=
    add_nonneg (add_nonneg (mul_nonneg ha hK) (mul_nonneg hb hm))
      (NativeMasterRHSCombination.rows_nonneg hΛ hm)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hC hs) (le_refl err))

/-- A finite family of original spaces shares one companion sequence.
The genuine stochastic master and true-energy relation are explicit
attachment premises here. The upper tail, finite ordinary budget,
strictly increasing smooth index and damping limit are chosen internally.
No convergence of the canonical smooth laws is required. -/
theorem exists_diagonal {ι:Type*}[Fintype ι](D:SmoothApproximation.ScalarData)
    (hβsmall:D.beta≤4/25)(C:ℝ)(hC:0≤C)(q:Fin 4→ℝ)(hq:16<q 3)
    (bad:ι→ℝ)(budget:ι→ℕ→ℕ→ℝ)(Λ:ℕ→ℝ)(hΛ1:∀k,1≤Λ k)
    (hΛ:Tendsto Λ atTop atTop)(J:ℕ→ℕ)(a b:ℝ→ℝ)
    (ha:Tendsto a atTop (𝓝 0))
    (hb:Tendsto (fun l=>energyScale D.beta l*b l) atTop (𝓝 0))
    (hb0:∀ᶠl:ℝ in atTop,0≤b l)
    (K m E:ι→ℕ→ℕ→ℕ→ℝ)
    (hK:∀i k L n,0<L→0≤K i k L n)
    (hm:∀i k L n,0<L→0≤m i k L n)
    (henergy:∀i k L n,0<L→m i k L n≤C*energyScale D.beta (Λ k)*K i k L n)
    (hE:∀i k L n,0<L→E i k L n≤
      (ScalarApproximationDiscrepancy.scalarError D n)^2*budget i k L)
    (hmaster:∀i k L n,0<L→
      ActualReferenceMasterClosure.Bound D.beta C (Λ k) (K i k L n) (m i k L n)
        (sqrt (E i k L n)+ActualTerminalReconstructionEnergy.error D n (J k) L+
          bad i*(Λ k)^(-(q 3/8))) (a (Λ k)) (b (Λ k)) 0 0):
    ∃L index:ℕ→ℕ,StrictMono index ∧ Tendsto index atTop atTop ∧
      (∀k,0<L k ∧ SmoothReferenceLimit.error D (index k)<(Λ k)^(-2:ℝ)/2) ∧
      ∀i:ι,Tendsto (fun k=>(Λ k)^2*(m i k (L k) (index k))^2) atTop (𝓝 0) ∧
        Tendsto (fun k=>(m i k (L k) (index k))^2) atTop (𝓝 0):=by
  classical
  let δ:ℕ→ℝ:=fun k=>(Λ k)^(-2:ℝ)/2
  have hδ(k:ℕ):0<δ k:=div_pos
    (rpow_pos_of_pos (zero_lt_one.trans_le (hΛ1 k)) _) (by norm_num)
  obtain ⟨L,index,hi,hit,happrox⟩:=SharedTerminalComparisonDiagonal.exists_index D budget J δ hδ
  let B:ℝ:=∑i:ι,|bad i|
  have hbad(i:ι):bad i≤B:=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (bad j)) (Finset.mem_univ i))
  have hbadevent:=hΛ.eventually
    (NativeHigherMasterFiniteCoefficient.bad_eventually q hq B (δ:=1/2) (by norm_num))
  have hcoeff:Tendsto (fun k=>C*a (Λ k)+C^2*energyScale D.beta (Λ k)*b (Λ k)) atTop (𝓝 0):=by
    have ht:=((ha.const_mul C).add (hb.const_mul (C^2))).comp hΛ
    simpa only [mul_zero,add_zero,mul_assoc,Function.comp_def] using ht
  obtain ⟨ε,hε,hclose⟩:=SequentialReferenceMasterCost.cost_limit D.beta_pos hβsmall hC
  have hloss:∀i:ActualReferenceMasterClosure.Row,
      0≤(0:ActualReferenceMasterClosure.Row→ℝ) i ∧ (0:ActualReferenceMasterClosure.Row→ℝ) i≤ε ∧
      0≤(0:ActualReferenceMasterClosure.Row→ℝ) i ∧ (0:ActualReferenceMasterClosure.Row→ℝ) i≤ε:=by
    intro i
    exact ⟨le_refl _,hε.le,le_refl _,hε.le⟩
  refine ⟨L,index,hi,hit,(fun k=>⟨(happrox k).1,(happrox k).2.1⟩),?_⟩
  intro i
  let M:ℕ→ℝ:=fun k=>m i k (L k) (index k)
  let KK:ℕ→ℝ:=fun k=>K i k (L k) (index k)
  let err:ℕ→ℝ:=fun k=>sqrt (E i k (L k) (index k))+
    ActualTerminalReconstructionEnergy.error D (index k) (J k) (L k)+bad i*(Λ k)^(-(q 3/8))
  have hfull:∀ᶠk:ℕ in atTop,0≤KK k ∧ 0≤M k ∧
      M k≤C*energyScale D.beta (Λ k)*KK k ∧ err k≤(Λ k)^(-2:ℝ) ∧
      ActualReferenceMasterClosure.Bound D.beta C (Λ k) (KK k) (M k) (err k)
        (a (Λ k)) (b (Λ k)) 0 0:=by
    filter_upwards [hbadevent] with k hk
    have hL:0<L k:=(happrox k).1
    refine ⟨hK i k (L k) (index k) hL,hm i k (L k) (index k) hL,
      henergy i k (L k) (index k) hL,?_,hmaster i k (L k) (index k) hL⟩
    have he: sqrt (E i k (L k) (index k))+
        ActualTerminalReconstructionEnergy.error D (index k) (J k) (L k)≤δ k:=
      (happrox k).2.2 i _ (hE i k (L k) (index k) hL)
    have hbi:bad i*(Λ k)^(-(q 3/8))≤(1/2:ℝ)*(Λ k)^(-2:ℝ):=
      (mul_le_mul_of_nonneg_right (hbad i) (rpow_nonneg (zero_le_one.trans (hΛ1 k)) _)).trans hk
    dsimp only [err,δ] at *
    linarith only [he,hbi]
  have hcost:=hclose 0 0 Λ KK M err (fun k=>a (Λ k)) (fun k=>b (Λ k)) hloss
    hΛ hcoeff (hΛ.eventually hb0) hfull
  exact ⟨hcost,SequentialReferenceMasterCost.energy_tendsto_zero hΛ (fun _=>sq_nonneg _) hcost⟩
end SHE.SharedCompanionCostLimit
