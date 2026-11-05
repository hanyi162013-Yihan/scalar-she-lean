module
public import SHE.LeftFrozenFiniteHaarConsistency
public import SHE.LeftFrozenHaarInput
public import SHE.BoundedHilbertItoCell
public import SHE.LeftFrozenFiniteHaarCells
public import SHE.LeftFrozenFiniteHaarIntegral
public import SHE.CommonLawLimit
public import SHE.FixedHaarIntegral
public import SHE.PredictableSteps
public import SHE.ContinuousPredictable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.LeftFrozenFiniteHaarFunctional
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand LeftFrozenFiniteHaarKernel
open ApproximationCells
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M Holder β:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
variable(U:ℝ≥0→Ω→StateL2)(hUa:StronglyAdapted 𝓕 U)



abbrev Source:=(ℝ≥0→StateL2)×(FiniteHaar.HaarNode→ℝ≥0→ℝ)

def functional(n:ℕ)(t:ℝ≥0)(z:Source):StateL2:=
  ∑k∈Finset.Icc 1 (index n t),∑i∈FiniteHaar.nodesBelow n,
    (z.2 i (min (point n k) t)-z.2 i (point n (k-1))) •
      (if point n (k-1)<t then
        NonlinearHaarIntegrand.kernel a ha ell M hell hb
          ((t:ℝ)-(point n (k-1):ℝ),z.1 (point n (k-1))) i else 0)

include hβ hHolder hholder in
theorem functional_measurable(n:ℕ)(t:ℝ≥0):Measurable (functional ha hell hb n t):=by
  apply Finset.measurable_sum
  intro k hk
  apply Finset.measurable_sum
  intro i hi
  have he(s:ℝ≥0):Measurable (fun z:Source=>z.2 i s):=by
    exact (measurable_pi_apply s).comp
      ((measurable_pi_apply i).comp (measurable_snd:Measurable (fun z:Source=>z.2)))
  have hs:Measurable (fun z:Source=>z.2 i (min (point n k) t)-z.2 i (point n (k-1))):=by
    exact (he _).sub (he _)
  have hc:Measurable (fun z:Source=>
      if point n (k-1)<t then
        NonlinearHaarIntegrand.kernel a ha ell M hell hb
          ((t:ℝ)-(point n (k-1):ℝ),z.1 (point n (k-1))) i else 0):=by
    split_ifs
    · exact (lp.evalCLM ℝ (fun _:FiniteHaar.HaarNode=>DyadicApproximation.RealL2) 2 i).continuous.measurable.comp
        ((NonlinearHaarIntegrand.kernel_measurable ha hell hb hβ hHolder hholder).comp
          (measurable_const.prodMk ((measurable_pi_apply _).comp measurable_fst)))
    · exact measurable_const
  exact hs.smul hc

theorem functional_eval(n:ℕ)(t:ℝ≥0)(X:FiniteHaar.HaarNode→ℝ≥0→Ω→ℝ)(ω:Ω):
    functional ha hell hb n t ((fun s=>U s ω),fun i s=>X i s ω)=
      LeftFrozenFiniteHaarIntegral.value ha hell hb U n t X ω:=by
  unfold functional LeftFrozenFiniteHaarIntegral.value
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  unfold LeftFrozenFiniteHaarCells.coefficient LeftFrozenHaarInput.coefficient
  split_ifs <;> rfl

variable {Ω':Type*}[MeasurableSpace Ω']
include hβ hHolder hholder in
/-- Common joint laws of an actual input path and its original driver
transfer through every concrete finite time/Haar stochastic sum. -/
theorem law(ν:Measure Ω')
    (V:ℝ≥0→Ω'→StateL2)
    (X:FiniteHaar.HaarNode→ℝ≥0→Ω→ℝ)(Y:FiniteHaar.HaarNode→ℝ≥0→Ω'→ℝ)
    (hU:∀s,Measurable (U s))(hV:∀s,Measurable (V s))
    (hX:∀i s,Measurable (X i s))(hY:∀i s,Measurable (Y i s))
    (hLaw:μ.map (fun ω=>((fun s=>U s ω),fun i s=>X i s ω))=
      ν.map (fun ω=>((fun s=>V s ω),fun i s=>Y i s ω)))
    (n:ℕ)(t:ℝ≥0):
    μ.map (LeftFrozenFiniteHaarIntegral.value ha hell hb U n t X)=
      ν.map (LeftFrozenFiniteHaarIntegral.value ha hell hb V n t Y):=by
  have hm:Measurable (functional ha hell hb n t):=
    functional_measurable ha hell hb hβ hHolder hholder n t
  have hu:Measurable (fun ω=>((fun s=>U s ω),fun i s=>X i s ω)):=
    (measurable_pi_iff.mpr hU).prodMk
      (measurable_pi_iff.mpr (fun i=>measurable_pi_iff.mpr (hX i)))
  have hv:Measurable (fun ω=>((fun s=>V s ω),fun i s=>Y i s ω)):=
    (measurable_pi_iff.mpr hV).prodMk
      (measurable_pi_iff.mpr (fun i=>measurable_pi_iff.mpr (hY i)))
  have hh:=congrArg (fun P:Measure Source=>P.map (functional ha hell hb n t)) hLaw
  rw [Measure.map_map hm hu,Measure.map_map hm hv] at hh
  simpa only [Function.comp_def,functional_eval] using hh
end SHE.LeftFrozenFiniteHaarFunctional
