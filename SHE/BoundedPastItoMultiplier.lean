module
public import SHE.PastParameterEnvelopeLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.BoundedPastItoMultiplier
open Set MeasureTheory PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable [CompleteSpace C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H v:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- A bounded scalar known at the original deterministic past pulls
through the original future Ito integral. This is DERIVED from event
locality and L2 closure, including unbounded Brownian outputs. -/
theorem exists_input (hlocal:StandardTerminalPastLocality J)
    (u:Process (E:=C) 𝓕 μ H)(Z:Ω→ℝ)(hZ:StronglyMeasurable[𝓕 v] Z)
    (M:ℝ)(hM:0≤M)(hb:∀ω,|Z ω|≤M):
    ∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun p=>if v<p.1 then Z p.2 • u p else 0) ∧
      J.integral input=ᵐ[μ] (fun ω=>Z ω*J.integral (post 𝓕 μ H v u) ω):=by
  let X:=Icc (-M) M
  let z:Ω→X:=fun ω=>⟨Z ω,(abs_le.mp (hb ω))⟩
  let g:X→(ℝ≥0×Ω)→C:=fun x p=>if v<p.1 then (x:ℝ) • u p else 0
  let K:X→Ω→ℝ:=fun x ω=>(x:ℝ)*J.integral (post 𝓕 μ H v u) ω
  have hz:StronglyMeasurable[𝓕 v] z:=
    hZ.measurable.subtype_mk.stronglyMeasurable
  have hc:∀ᵐp∂energyMeasure μ H,Continuous (fun x:X=>g x p):=by
    filter_upwards with p
    dsimp only [g]
    split_ifs
    · exact continuous_subtype_val.smul continuous_const
    · exact continuous_const
  have hzero:∀x p,p.1≤v→g x p=0:=by
    intro x p hp
    exact if_neg (not_lt.mpr hp)
  have hKm:∀x,Measurable (K x):=fun x=>
    measurable_const.mul (Lp.stronglyMeasurable (J.integral (post 𝓕 μ H v u))).measurable
  have hKc:∀ω,Continuous (fun x:X=>K x ω):=fun ω=>
    continuous_subtype_val.mul continuous_const
  let B:Ω→ℝ:=fun ω=>M*‖J.integral (post 𝓕 μ H v u) ω‖
  have hB:MemLp B 2 μ:=((Lp.memLp (J.integral (post 𝓕 μ H v u))).norm).const_mul M
  have hB0:∀ω,0≤B ω:=fun ω=>mul_nonneg hM (norm_nonneg _)
  have hKb:∀x ω,‖K x ω‖≤B ω:=by
    intro x ω
    rw [show K x ω=(x:ℝ)*J.integral (post 𝓕 μ H v u) ω from rfl,norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr x.2) (norm_nonneg _)
  have hrep:∀x:X,∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] g x ∧ J.integral input=ᵐ[μ] K x:=by
    intro x
    refine ⟨(x:ℝ) • post 𝓕 μ H v u,?_,?_⟩
    · filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_smul (x:ℝ) (post 𝓕 μ H v u)),
        post_ae 𝓕 μ H v u] with p hs hp
      rw [hs]
      change (x:ℝ) • post 𝓕 μ H v u p=g x p
      rw [hp]
      dsimp only [g]
      split_ifs <;> simp
    · rw [map_smul]
      exact Lp.coeFn_smul (x:ℝ) (J.integral (post 𝓕 μ H v u))
  obtain ⟨input,hi,hJ⟩:=PastParameterEnvelopeLimit.original_input
    𝓕 μ H v J hlocal g hc hzero K hKm hKc B hB hB0 hKb hrep hz
  exact ⟨input,hi,hJ⟩

/-- The genuine original scalar time-cell integration rule, retaining
the original stopped-integral increment and a coefficient known at v. -/
theorem increment (hlocal:StandardTerminalPastLocality J)
    (r:ℝ≥0)(hvr:v≤r)(u:Process (E:=C) 𝓕 μ H)
    (Z:Ω→ℝ)(hZ:StronglyMeasurable[𝓕 v] Z)(M:ℝ)(hM:0≤M)(hb:∀ω,|Z ω|≤M):
    ∃input:Process (E:=C) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun p=>if v<p.1 ∧ p.1<r then Z p.2 • u p else 0) ∧
      J.integral input=ᵐ[μ] (fun ω=>Z ω*(J.integral (StoppedItoInputs.stop 𝓕 μ H r u) ω-
        J.integral (StoppedItoInputs.stop 𝓕 μ H v u) ω)):=by
  obtain ⟨input,hi,hJ⟩:=exists_input 𝓕 μ H v J hlocal
    (StoppedItoInputs.stop 𝓕 μ H r u) Z hZ M hM hb
  refine ⟨input,?_,?_⟩
  · filter_upwards [hi,StoppedItoInputs.stop_ae 𝓕 μ H r u] with p hp hs
    rw [hp,hs]
    by_cases hvp:v<p.1 <;> by_cases hpr:p.1<r <;>
      simp only [hvp,hpr,StoppedItoInputs.before,Set.indicator,Set.mem_setOf_eq,
        NNReal.coe_lt_coe,ite_true,ite_false,true_and,false_and,and_false,smul_zero]
  · filter_upwards [hJ,Lp.coeFn_sub (J.integral (StoppedItoInputs.stop 𝓕 μ H r u))
      (J.integral (StoppedItoInputs.stop 𝓕 μ H v u))] with ω hj ho
    rw [PastItoAlgebra.post_stop_eq_sub 𝓕 μ H v r hvr u,map_sub,ho] at hj
    exact hj
end SHE.BoundedPastItoMultiplier
