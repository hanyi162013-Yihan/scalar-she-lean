module
public import SHE.StandardTerminalPastLocality
public import SHE.PredictableSquareDominatedLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.FinitePastMaskLocality
open Set MeasureTheory PredictableL2 PastItoInputs Filter Topology Classical
open scoped NNReal ENNReal BigOperators
variable {Ω C E:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C]
variable [NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (m:ℕ→ℕ)(r:ℕ→ℕ→ℝ≥0)(A:ℕ→ℕ→Set Ω)
variable (hA:∀n i,MeasurableSet[𝓕 (r n i)] (A n i))

def mask(n:ℕ)(p:ℝ≥0×Ω):ℝ:=
  ∑i∈Finset.range (m n),if r n i<p.1 ∧ p.2∈A n i then 1 else 0

def approximation(f:Process (E:=C) 𝓕 μ H)(n:ℕ):Process (E:=C) 𝓕 μ H:=
  ∑i∈Finset.range (m n),eventProcess 𝓕 μ H (r n i) (A n i) (hA n i) f

theorem approximation_ae(f:Process (E:=C) 𝓕 μ H)(n:ℕ):
    approximation 𝓕 μ H m r A hA f n=ᵐ[energyMeasure μ H]
      (fun p=>mask m r A n p • f p):=by
  have hs:=ae_eq_of_ae_eq_trim (Lp.coeFn_fun_finsetSum (Finset.range (m n))
    (fun i=>eventProcess 𝓕 μ H (r n i) (A n i) (hA n i) f))
  filter_upwards [hs,ae_all_iff.mpr (fun i=>eventProcess_ae 𝓕 μ H (r n i) (A n i) (hA n i) f)] with p hp hi
  change approximation 𝓕 μ H m r A hA f n p=_ at hp ⊢
  rw [hp]
  unfold mask
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  by_cases hc:r n i<p.1 ∧ p.2∈A n i
  · simp [eventAfter,Set.indicator_apply,mem_prod,mem_Ioi,hc.1,hc.2]
  · simp only [eventAfter,Set.indicator_apply,mem_prod,mem_Ioi,hc,ite_false,zero_smul]

theorem integral_zero
    (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (B:Set Ω)(hB:∀n i,i<m n→Disjoint B (A n i))
    (f:Process (E:=C) 𝓕 μ H)(n:ℕ):
    ∀ᵐω∂μ,ω∈B→J.integral (approximation 𝓕 μ H m r A hA f n) ω=0:=by
  have hs:=Lp.coeFn_fun_finsetSum (Finset.range (m n))
    (fun i=>J.integral (eventProcess 𝓕 μ H (r n i) (A n i) (hA n i) f))
  have he:J.integral (approximation 𝓕 μ H m r A hA f n)=
      ∑i∈Finset.range (m n),J.integral (eventProcess 𝓕 μ H (r n i) (A n i) (hA n i) f):=by
    simp only [approximation,map_sum]
  rw [←he] at hs
  filter_upwards [hs,ae_all_iff.mpr (fun i=>hlocal (r n i) (A n i) (hA n i) f)] with ω hs hi hω
  rw [hs]
  apply Finset.sum_eq_zero
  intro i hmem
  rw [hi i,Set.indicator_of_notMem]
  exact fun ha=>Set.disjoint_left.mp (hB n i (Finset.mem_range.mp hmem)) hω ha

include hA

/-- A finite first-exit approximation transfers deterministic-past
locality to its actual L2 limit. The masks are the only deterministic
input; the same original integral supplies every approximation. -/
theorem limit
    (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (B:Set Ω)(hB:∀n i,i<m n→Disjoint B (A n i))
    (f:Process (E:=C) 𝓕 μ H)
    (hb:∀n p,0≤mask m r A n p ∧ mask m r A n p≤1)
    (hl:∀ᵐp∂energyMeasure μ H,f p=0 ∨
      Tendsto (fun n=>mask m r A n p) atTop (𝓝 1)):
    ∀ᵐω∂μ,ω∈B→J.integral f ω=0:=by
  let g:=approximation 𝓕 μ H m r A hA f
  have hg:∀n,g n=ᵐ[energyMeasure μ H] (fun p=>mask m r A n p • f p):=
    fun n=>approximation_ae 𝓕 μ H m r A hA f n
  have hi:Integrable (fun p=>‖f p‖^2) (energyMeasure μ H):=
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp f)).norm.integrable_sq
  have hgb:∀n,∀ᵐp∂energyMeasure μ H,‖g n p‖^2≤‖f p‖^2:=by
    intro n
    filter_upwards [hg n] with p hp
    have hn:‖g n p‖≤‖f p‖:=by
      rw [hp,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hb n p).1]
      nlinarith only [(hb n p).2,norm_nonneg (f p)]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hgl:∀ᵐp∂energyMeasure μ H,Tendsto (fun n=>g n p) atTop (𝓝 (f p)):=by
    filter_upwards [hl,ae_all_iff.mpr hg] with p hp hr
    have he:(fun n=>g n p)=(fun n=>mask m r A n p • f p):=funext (fun n=>hr n)
    rw [he]
    rcases hp with hp|hp
    · simp only [hp,smul_zero]
      exact tendsto_const_nhds
    · simpa only [one_smul] using hp.smul (tendsto_const_nhds (x:=f p))
  have ht:=PredictableSquareDominatedLimit.tendsto 𝓕 μ H g f (fun p=>‖f p‖^2) hi hgb
    (ae_of_all _ (fun _=>le_rfl)) hgl
  have hj:=J.integral.continuous.tendsto f |>.comp ht
  obtain ⟨ns,hns,hae⟩:=(tendstoInMeasure_of_tendsto_Lp hj).exists_seq_tendsto_ae
  filter_upwards [hae,ae_all_iff.mpr (fun n=>integral_zero 𝓕 μ H m r A hA J hlocal B hB f n)] with ω hl hn hω
  have he:(fun n=>J.integral (g (ns n)) ω)=(fun _=> (0:E)):=
    funext (fun n=>hn (ns n) hω)
  change Tendsto (fun n=>J.integral (g (ns n)) ω) atTop (𝓝 (J.integral f ω)) at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds
end SHE.FinitePastMaskLocality
