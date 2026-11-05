module
public import SHE.SequentialMasterCost
public import SHE.ActualReferenceMasterClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace SHE.SequentialReferenceMasterCost
open Filter Topology Real

/-- Conditional numerical closure after the ACTUAL stochastic finite
master is attached. This theorem does not supply that comparison;
it carries its proved bounds through the chosen smoothing diagonal. -/
theorem cost_limit {β C:ℝ}(hβ:0<β)(hβsmall:β≤4/25)(hC:0≤C):
    ∃ε:ℝ,0<ε ∧ ∀(δ η:ActualReferenceMasterClosure.Row→ℝ)(Λ K m err a b:ℕ→ℝ),
      (∀i,0≤δ i ∧ δ i≤ε ∧ 0≤η i ∧ η i≤ε)→
      Tendsto Λ atTop atTop→
      Tendsto (fun k=>C*a k+C^2*energyScale β (Λ k)*b k) atTop (𝓝 (0:ℝ))→
      (∀ᶠk in atTop,0≤b k)→
      (∀ᶠk in atTop,0≤K k ∧ 0≤m k ∧
        m k≤C*energyScale β (Λ k)*K k ∧ err k≤(Λ k)^(-2:ℝ) ∧
        ActualReferenceMasterClosure.Bound β C (Λ k) (K k) (m k) (err k) (a k) (b k) δ η)→
      Tendsto (fun k=>(Λ k)^2*(m k)^2) atTop (𝓝 0):=by
  obtain ⟨ε,hε,hclose⟩:=ActualReferenceMasterClosure.decay hβ hβsmall hC
  refine ⟨ε,hε,?_⟩
  intro δ η Λ K m err a b hl hΛ hcoeff hb hfull
  have hsmall:=hcoeff.eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1/2))
  apply SequentialMasterCost.damping_cost (p:=(5/2:ℝ)) (C:=ActualReferenceMasterClosure.constant β C^2) (by norm_num) hΛ
  filter_upwards [hfull,hsmall,hb,hΛ.eventually (eventually_ge_atTop (1:ℝ))] with k hk hs hb hL
  have hm:=hclose δ η (Λ k) (K k) (m k) (err k) (a k) (b k) hl hL
    hk.1 hk.2.1 hk.2.2.1 hb hs.le hk.2.2.2.1 hk.2.2.2.2
  refine ⟨sq_nonneg _,?_⟩
  have hp:=pow_le_pow_left₀ hk.2.1 hm 2
  calc
    _≤(ActualReferenceMasterClosure.constant β C*(Λ k)^(-(5/4:ℝ)))^2:=hp
    _=_:=by
      rw [mul_pow,←rpow_mul_natCast (zero_le_one.trans hL)]
      norm_num

/-- Vanishing true damping cost controls the underlying energy on the
same selected diagonal. The approximation index need not be fixed. -/
theorem energy_tendsto_zero {Λ E : ℕ→ℝ} (hΛ : Tendsto Λ atTop atTop)
    (hE : ∀k,0≤E k)
    (hc : Tendsto (fun k=>(Λ k)^2*E k) atTop (𝓝 0)) :
    Tendsto E atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall hE) ?_ hc
  filter_upwards [hΛ.eventually (eventually_ge_atTop (1:ℝ))] with k hk
  have hs : (1:ℝ)≤(Λ k)^2 := by nlinarith only [hk]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (hE k)

end SHE.SequentialReferenceMasterCost
