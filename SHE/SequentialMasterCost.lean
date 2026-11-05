module
public import SHE.ActualLinearMasterClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace SHE.SequentialMasterCost
open Filter Topology Real

/-- The damping-cost argument is valid along the deterministic sequence
on which the smooth companion and finite cutoffs were selected. -/
theorem damping_cost {Λ M:ℕ→ℝ}{C p:ℝ}(hp:2<p)(hΛ:Tendsto Λ atTop atTop)
    (hM:∀ᶠk in atTop,0≤M k ∧ M k≤C*(Λ k)^(-p)):
    Tendsto (fun k=>(Λ k)^2*M k) atTop (𝓝 0):=by
  have hlim:Tendsto (fun k:ℕ=>C*(Λ k)^(-(p-2))) atTop (𝓝 0):=by
    simpa only [Function.comp_def,mul_zero] using
      ((tendsto_rpow_neg_atTop (by linarith:0<p-2)).comp hΛ).const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hM] with k hk
    exact mul_nonneg (sq_nonneg _) hk.1
  · filter_upwards [hM,hΛ.eventually (eventually_gt_atTop (0:ℝ))] with k hk hΛk
    calc
      _≤(Λ k)^2*(C*(Λ k)^(-p)):=mul_le_mul_of_nonneg_left hk.2 (sq_nonneg _)
      _=C*(Λ k)^(-(p-2)):=by
        rw [←rpow_natCast (Λ k) 2,mul_left_comm,←rpow_add hΛk]
        congr 1
        norm_num
        ring

/-- Conditional numerical closure after the ACTUAL stochastic finite
master is attached. This theorem does not supply that comparison;
it carries its proved bounds through the chosen smoothing diagonal. -/
theorem cost_limit {β C:ℝ}(hβ:0<β)(hβsmall:β≤4/25)(hC:0≤C):
    ∃ε:ℝ,0<ε ∧ ∀(δ η:MasterRow→ℝ)(Λ K m err a b:ℕ→ℝ),
      (∀i,0≤δ i ∧ δ i≤ε ∧ 0≤η i ∧ η i≤ε)→
      Tendsto Λ atTop atTop→
      Tendsto (fun k=>C*a k+C^2*energyScale β (Λ k)*b k) atTop (𝓝 (0:ℝ))→
      (∀ᶠk in atTop,0≤b k)→
      (∀ᶠk in atTop,0≤K k ∧ 0≤m k ∧
        m k≤C*energyScale β (Λ k)*K k ∧ err k≤(Λ k)^(-2:ℝ) ∧
        ActualLinearMasterClosure.Bound β C (Λ k) (K k) (m k) (err k) (a k) (b k) δ η)→
      Tendsto (fun k=>(Λ k)^2*(m k)^2) atTop (𝓝 0):=by
  obtain ⟨ε,hε,hclose⟩:=ActualLinearMasterClosure.decay hβ hβsmall hC
  refine ⟨ε,hε,?_⟩
  intro δ η Λ K m err a b hl hΛ hcoeff hb hfull
  have hsmall:=hcoeff.eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1/2))
  apply damping_cost (p:=(5/2:ℝ)) (C:=ZeroNativeDyadicMaster.constant β C^2) (by norm_num) hΛ
  filter_upwards [hfull,hsmall,hb,hΛ.eventually (eventually_ge_atTop (1:ℝ))] with k hk hs hb hL
  have hm:=hclose δ η (Λ k) (K k) (m k) (err k) (a k) (b k) hl hL
    hk.1 hk.2.1 hk.2.2.1 hb hs.le hk.2.2.2.1 hk.2.2.2.2
  refine ⟨sq_nonneg _,?_⟩
  have hp:=pow_le_pow_left₀ hk.2.1 hm 2
  calc
    _≤(ZeroNativeDyadicMaster.constant β C*(Λ k)^(-(5/4:ℝ)))^2:=hp
    _=_:=by
      rw [mul_pow,←rpow_mul_natCast (zero_le_one.trans hL)]
      norm_num
end SHE.SequentialMasterCost
