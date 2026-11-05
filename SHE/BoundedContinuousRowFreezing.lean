module
public import SHE.LeftFrozenHaarKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.BoundedContinuousRowFreezing
open MeasureTheory Set Filter PredictableL2
open scoped NNReal ENNReal Topology
variable {Ω E C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [NormedAddCommGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (q : ℝ≥0) (R : Iic q×E→C) (U : ℝ≥0→Ω→E)

def time (n : ℕ) (s : ℝ≥0) : Iic q :=
  ⟨min (LeftFrozenHaarKernel.past n s) q,min_le_right _ _⟩

def value (n : ℕ) (p : ℝ≥0×Ω) : C :=
  if p.1<q then R (time q n p.1,U (LeftFrozenHaarKernel.past n p.1) p.2) else 0

def target (p : ℝ≥0×Ω) : C :=
  if p.1<q then R (⟨min p.1 q,min_le_right _ _⟩,U p.1 p.2) else 0

theorem time_measurable (n : ℕ) : Measurable (time q n) :=
  ((LeftFrozenHaarKernel.past_measurable n).min measurable_const).subtype_mk

theorem value_measurable (hR : Continuous R) (hU : Measurable (Function.uncurry U)) (n : ℕ) :
    Measurable (value q R U n) := by
  have hs : Measurable (fun p:ℝ≥0×Ω=>LeftFrozenHaarKernel.past n p.1) :=
    (LeftFrozenHaarKernel.past_measurable n).comp measurable_fst
  exact (hR.measurable.comp (((time_measurable q n).comp measurable_fst).prodMk
    (hU.comp (hs.prodMk measurable_snd)))).ite
      (measurableSet_lt measurable_fst measurable_const) measurable_const

theorem target_measurable (hR : Continuous R) (hU : Measurable (Function.uncurry U)) :
    Measurable (target q R U) := by
  have hs : Measurable (fun p:ℝ≥0×Ω=>(⟨min p.1 q,min_le_right _ _⟩:Iic q)) :=
    (measurable_fst.min measurable_const).subtype_mk
  exact (hR.measurable.comp (hs.prodMk hU)).ite
    (measurableSet_lt measurable_fst measurable_const) measurable_const

/-- Actual continuous state paths give pointwise consistency of the
bounded original rows frozen at deterministic left endpoints. -/
theorem value_tendsto (hR : Continuous R) (hc : ∀ω,Continuous (fun s=>U s ω)) (p : ℝ≥0×Ω) :
    Tendsto (fun n=>value q R U n p) atTop (𝓝 (target q R U p)) := by
  by_cases hp : p.1<q
  · have ht : Tendsto (fun n=>time q n p.1) atTop
        (𝓝 (⟨min p.1 q,min_le_right _ _⟩:Iic q)) := by
      apply tendsto_subtype_rng.mpr
      exact (LeftFrozenHaarKernel.past_tendsto p.1).min tendsto_const_nhds
    have hu := ((hc p.2).tendsto p.1).comp (LeftFrozenHaarKernel.past_tendsto p.1)
    simpa only [Function.comp_def,value,target,ite_eq_left hp] using
      (hR.tendsto _).comp (ht.prodMk_nhds hu)
  · simpa only [value,target,ite_eq_right hp] using (tendsto_const_nhds (x:=(0:C)))

/-- Actual bounded rough rows converge in the original time/sample L2
energy. The bound is uniform over every deterministic left grid. -/
theorem energy_tendsto (μ : Measure Ω) [IsFiniteMeasure μ] (H : ℝ≥0)
    (hR : Continuous R) (hU : Measurable (Function.uncurry U))
    (hc : ∀ω,Continuous (fun s=>U s ω)) (M : ℝ) (hM : 0≤M)
    (hb : ∀p,‖R p‖≤M) :
    Tendsto (fun n=>∫p,‖value q R U n p-target q R U p‖^2 ∂energyMeasure μ H)
      atTop (𝓝 (0:ℝ)) := by
  have hfin : IsFiniteMeasure (energyMeasure μ H) := by
    dsimp only [energyMeasure]
    infer_instance
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun p=>‖value q R U n p-target q R U p‖^2) (energyMeasure μ H) :=
    (((value_measurable q R U hR hU n).sub (target_measurable q R U hR hU)).norm.pow_const 2).aestronglyMeasurable
  have hv (n : ℕ) (p : ℝ≥0×Ω) : ‖value q R U n p‖≤M := by
    dsimp only [value]
    split_ifs
    · exact hb _
    · simpa only [norm_zero] using hM
  have ht (p : ℝ≥0×Ω) : ‖target q R U p‖≤M := by
    dsimp only [target]
    split_ifs
    · exact hb _
    · simpa only [norm_zero] using hM
  have hbound (n : ℕ) : ∀ᵐp∂energyMeasure μ H,
      ‖‖value q R U n p-target q R U p‖^2‖≤(2*M)^2 := by
    filter_upwards with p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hv n p,ht p])
  have hlimit : ∀ᵐp∂energyMeasure μ H,
      Tendsto (fun n=>‖value q R U n p-target q R U p‖^2) atTop (𝓝 (0:ℝ)) := by
    filter_upwards with p
    have he := ((value_tendsto q R U hR hc p).sub_const (target q R U p)).norm.pow 2
    simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using he
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _p:ℝ≥0×Ω=>(2*M)^2) hm
      (integrable_const _) hbound hlimit
end SHE.BoundedContinuousRowFreezing
