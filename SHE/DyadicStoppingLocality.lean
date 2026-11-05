module
public import SHE.DyadicFirstExitMasks
public import SHE.FinitePastMaskLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.DyadicStoppingLocality
open Set MeasureTheory PredictableL2 PastItoInputs Filter Topology Classical
open scoped NNReal ENNReal BigOperators
variable {Ω C E:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C]
variable [NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)

/-- Random first-exit locality is DERIVED from deterministic-past
pullout and the same integral's L2 isometry, using finite dyadic events. -/
theorem vanish
    (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (A:ℝ≥0→Ω→ℝ)(ha:StronglyAdapted 𝓕 A)(hc:∀ω,Continuous (fun s=>A s ω))
    (hm:∀ω,Monotone (fun s=>A s ω))(r:ℝ)(hH:0<H)
    (f:Process (E:=C) 𝓕 μ H)
    (hf:∀ᵐp∂energyMeasure μ H,A p.1 p.2≤r→f p=0):
    ∀ᵐω∂μ,A H ω≤r→J.integral f ω=0:=by
  let m:ℕ→ℕ:=fun n=>ApproximationCells.index n H
  let grid:ℕ→ℕ→ℝ≥0:=ApproximationCells.point
  let events:=DyadicFirstExitMasks.event A r
  have hE:∀n i,MeasurableSet[𝓕 (grid n i)] (events n i):=
    DyadicFirstExitMasks.measurable_event 𝓕 A ha r
  have he(n:ℕ)(p:ℝ≥0×Ω):FinitePastMaskLocality.mask m grid events n p=
      DyadicFirstExitMasks.mask A r n H p.1 p.2:=by
    unfold FinitePastMaskLocality.mask DyadicFirstExitMasks.mask
    apply Finset.sum_congr rfl
    intro i _
    simp only [grid,events,and_comm]
  have hB:∀n i,i<m n→Disjoint {ω|A H ω≤r} (events n i):=by
    intro n i hi
    apply Set.disjoint_left.mpr
    intro ω hω hE
    have hp:=hm ω (DyadicFirstExitMasks.point_lt n hH hi).le
    exact (not_lt_of_ge (hp.trans hω)) hE.1
  have hb:∀n p,0≤FinitePastMaskLocality.mask m grid events n p ∧
      FinitePastMaskLocality.mask m grid events n p≤1:=by
    intro n p
    rw [he]
    exact DyadicFirstExitMasks.mask_bounds A r n H p.1 p.2
  have hs:∀ᵐp∂energyMeasure μ H,0<p.1 ∧ p.1≤H:=
    (Measure.quasiMeasurePreserving_fst (μ:=timeMeasure H) (ν:=μ)).ae (timeMeasure_ae_mem H)
  have hl:∀ᵐp∂energyMeasure μ H,f p=0 ∨
      Tendsto (fun n=>FinitePastMaskLocality.mask m grid events n p) atTop (𝓝 1):=by
    filter_upwards [hf,hs] with p hp hs
    by_cases ht:A p.1 p.2≤r
    · exact Or.inl (hp ht)
    · right
      have hv:=DyadicFirstExitMasks.mask_eventually_one A hc r H p.1 hs.1 hs.2 p.2 (lt_of_not_ge ht)
      have ht':Tendsto (fun _n:ℕ=>(1:ℝ)) atTop (𝓝 1):=tendsto_const_nhds
      apply ht'.congr'
      filter_upwards [hv] with n hn
      exact (he n p).trans hn |>.symm
  exact FinitePastMaskLocality.limit 𝓕 μ H m grid events hE J hlocal {ω|A H ω≤r} hB f hb hl
end SHE.DyadicStoppingLocality
