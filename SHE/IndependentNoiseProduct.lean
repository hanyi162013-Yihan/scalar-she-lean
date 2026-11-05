module
public import SHE.NativePathLawComparison
public import SHE.ContinuousPredictable
public import Mathlib.Probability.Independence.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.IndependentNoiseProduct
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable {Ω Ξ E:Type*}[MeasurableSpace Ω][MeasurableSpace Ξ]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)

/-- The actual filtration on an independent probability product. -/
def filtration:Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω×Ξ)) where
  seq t:=(𝓕 t).prod (𝓖 t)
  mono' s t hst:=sup_le_sup (MeasurableSpace.comap_mono (𝓕.mono hst))
    (MeasurableSpace.comap_mono (𝓖.mono hst))
  le' t:=sup_le_sup (MeasurableSpace.comap_mono (𝓕.le t))
    (MeasurableSpace.comap_mono (𝓖.le t))

/-- Forgetting the independent auxiliary coordinate preserves the actual
predictable sigma algebra, not merely ambient joint measurability. -/
theorem predictable_fst:@Measurable (ℝ≥0×(Ω×Ξ)) (ℝ≥0×Ω)
    (filtration 𝓕 𝓖).predictable 𝓕.predictable (fun p=>(p.1,p.2.1)):=by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[(filtration 𝓕 𝓖).predictable]
      ((fun p:ℝ≥0×(Ω×Ξ)=>(p.1,p.2.1)) ⁻¹' ({⊥}×ˢA))
    change MeasurableSet[(filtration 𝓕 𝓖).predictable] ({⊥}×ˢ(Prod.fst ⁻¹' A))
    apply measurableSet_predictable_singleton_bot_prod
    exact @measurable_fst Ω Ξ (𝓕 ⊥) (𝓖 ⊥) A hA
  · intro t A hA
    change MeasurableSet[(filtration 𝓕 𝓖).predictable]
      ((fun p:ℝ≥0×(Ω×Ξ)=>(p.1,p.2.1)) ⁻¹' ((Ioi t)×ˢA))
    change MeasurableSet[(filtration 𝓕 𝓖).predictable] ((Ioi t)×ˢ(Prod.fst ⁻¹' A))
    apply measurableSet_predictable_Ioi_prod
    exact @measurable_fst Ω Ξ (𝓕 t) (𝓖 t) A hA

variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

def state(U:ℝ≥0→Ω→E):ℝ≥0→Ω×Ξ→E:=fun t z=>U t z.1

theorem state_continuous(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω)):
    ∀z:Ω×Ξ,Continuous (fun t=>state U t z):=fun z=>hc z.1

theorem state_predictable(U:ℝ≥0→Ω→E)
    (hU:StronglyMeasurable[𝓕.predictable] (Function.uncurry U)):
    StronglyMeasurable[(filtration 𝓕 𝓖).predictable] (Function.uncurry (state (Ξ:=Ξ) U)):=
  hU.comp_measurable (predictable_fst 𝓕 𝓖)

/-- The independent extension preserves the supplied continuous-path law
exactly, on the original native interval. -/
theorem state_law(μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
    (H:ℝ≥0)(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω))
    (hU:Measurable (Function.uncurry U)):
    NativePathLawComparison.law H (μ.prod ν) (state (Ξ:=Ξ) U) (state_continuous U hc)=
      NativePathLawComparison.law H μ U hc:=by
  apply Subtype.ext
  change (μ.prod ν).map (NativeContinuousPath.path H (state U) (state_continuous U hc))=
    μ.map (NativeContinuousPath.path H U hc)
  have he:NativeContinuousPath.path H (state (Ξ:=Ξ) U) (state_continuous U hc)=
      (NativeContinuousPath.path H U hc)∘Prod.fst:=rfl
  rw [he,←Measure.map_map (NativeContinuousPath.measurable_path H U hc hU) measurable_fst,
    (measurePreserving_fst (μ:=μ) (ν:=ν)).map_eq]

/-- Every observable of the old space is independent of every auxiliary
observable on the genuine product probability. -/
theorem independent{A C:Type*}[MeasurableSpace A][MeasurableSpace C]
    (μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
    (f:Ω→A)(g:Ξ→C)(hf:Measurable f)(hg:Measurable g):
    ProbabilityTheory.IndepFun (fun z:Ω×Ξ=>f z.1) (fun z:Ω×Ξ=>g z.2) (μ.prod ν):=
  ProbabilityTheory.indepFun_prod hf hg

end SHE.IndependentNoiseProduct
