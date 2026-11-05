module
public import SHE.IndependentNoiseProduct
public import SHE.NullCompleteFiltration
public import Mathlib.MeasureTheory.Measure.NullMeasurable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.IndependentNoiseCompletion
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable {Ω Ξ E:Type*}[MeasurableSpace Ω][MeasurableSpace Ξ]
variable (μ:Measure Ω)(ν:Measure Ξ)

abbrev Space:=NullMeasurableSpace (Ω×Ξ) (μ.prod ν)
def measure:Measure (Space μ ν):=(μ.prod ν).completion
instance [IsProbabilityMeasure μ][IsProbabilityMeasure ν]:IsProbabilityMeasure (measure μ ν):=by
  constructor
  change (μ.prod ν) univ=1
  simp

def nullSigma:MeasurableSpace (Ω×Ξ):=
  MeasurableSpace.generateFrom {A:Set (Ω×Ξ)|(μ.prod ν) A=0}

variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
/-- Complete the actual independent product filtration with all joint
null sets. No stochastic integral or equation is part of this definition. -/
def filtration:Filtration ℝ≥0 (inferInstance:MeasurableSpace (Space μ ν)) where
  seq t:=(IndependentNoiseProduct.filtration 𝓕 𝓖) t⊔nullSigma μ ν
  mono' _ _ h:=sup_le_sup ((IndependentNoiseProduct.filtration 𝓕 𝓖).mono h) le_rfl
  le' t:=by
    apply sup_le
    · intro A hA
      exact ((IndependentNoiseProduct.filtration 𝓕 𝓖).le t A hA).nullMeasurableSet
    · apply MeasurableSpace.generateFrom_le
      intro A hA
      exact NullMeasurableSet.of_null hA

theorem contains_null:NullCompleteFiltration.ContainsNullSets (filtration μ ν 𝓕 𝓖) (measure μ ν):=by
  intro t A hA
  change MeasurableSet[((IndependentNoiseProduct.filtration 𝓕 𝓖) t)⊔nullSigma μ ν] A
  exact (le_sup_right:nullSigma μ ν≤((IndependentNoiseProduct.filtration 𝓕 𝓖) t)⊔nullSigma μ ν) A
    (MeasurableSpace.measurableSet_generateFrom hA)

theorem fst_measurable:@Measurable (Space μ ν) Ω inferInstance inferInstance Prod.fst:=
  measurable_fst.nullMeasurable.measurable'

theorem snd_measurable:@Measurable (Space μ ν) Ξ inferInstance inferInstance Prod.snd:=
  measurable_snd.nullMeasurable.measurable'

theorem fst_preserving[IsProbabilityMeasure μ][IsProbabilityMeasure ν]:
    @MeasurePreserving (Space μ ν) Ω inferInstance inferInstance Prod.fst (measure μ ν) μ:=by
  refine ⟨fst_measurable μ ν,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (fst_measurable μ ν) hA]
  exact (measurePreserving_fst (μ:=μ) (ν:=ν)).measure_preimage hA.nullMeasurableSet

theorem snd_preserving[IsProbabilityMeasure μ][IsProbabilityMeasure ν]:
    @MeasurePreserving (Space μ ν) Ξ inferInstance inferInstance Prod.snd (measure μ ν) ν:=by
  refine ⟨snd_measurable μ ν,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (snd_measurable μ ν) hA]
  exact (measurePreserving_snd (μ:=μ) (ν:=ν)).measure_preimage hA.nullMeasurableSet

theorem predictable_fst:@Measurable (ℝ≥0×Space μ ν) (ℝ≥0×Ω)
    (filtration μ ν 𝓕 𝓖).predictable 𝓕.predictable (fun p=>(p.1,p.2.1)):=by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[(filtration μ ν 𝓕 𝓖).predictable] ({⊥}×ˢ(Prod.fst ⁻¹' A))
    apply measurableSet_predictable_singleton_bot_prod
    change MeasurableSet[((IndependentNoiseProduct.filtration 𝓕 𝓖) ⊥)⊔nullSigma μ ν] (Prod.fst ⁻¹' A)
    exact (le_sup_left:((IndependentNoiseProduct.filtration 𝓕 𝓖) ⊥)≤((IndependentNoiseProduct.filtration 𝓕 𝓖) ⊥)⊔nullSigma μ ν) _
      (@measurable_fst Ω Ξ (𝓕 ⊥) (𝓖 ⊥) A hA)
  · intro t A hA
    change MeasurableSet[(filtration μ ν 𝓕 𝓖).predictable] ((Ioi t)×ˢ(Prod.fst ⁻¹' A))
    apply measurableSet_predictable_Ioi_prod
    change MeasurableSet[((IndependentNoiseProduct.filtration 𝓕 𝓖) t)⊔nullSigma μ ν] (Prod.fst ⁻¹' A)
    exact (le_sup_left:((IndependentNoiseProduct.filtration 𝓕 𝓖) t)≤((IndependentNoiseProduct.filtration 𝓕 𝓖) t)⊔nullSigma μ ν) _
      (@measurable_fst Ω Ξ (𝓕 t) (𝓖 t) A hA)

theorem predictable_snd:@Measurable (ℝ≥0×Space μ ν) (ℝ≥0×Ξ)
    (filtration μ ν 𝓕 𝓖).predictable 𝓖.predictable (fun p=>(p.1,p.2.2)):=by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[(filtration μ ν 𝓕 𝓖).predictable] ({⊥}×ˢ(Prod.snd ⁻¹' A))
    apply measurableSet_predictable_singleton_bot_prod
    change MeasurableSet[((IndependentNoiseProduct.filtration 𝓕 𝓖) ⊥)⊔nullSigma μ ν] (Prod.snd ⁻¹' A)
    exact (le_sup_left:((IndependentNoiseProduct.filtration 𝓕 𝓖) ⊥)≤((IndependentNoiseProduct.filtration 𝓕 𝓖) ⊥)⊔nullSigma μ ν) _
      (@measurable_snd Ω Ξ (𝓕 ⊥) (𝓖 ⊥) A hA)
  · intro t A hA
    change MeasurableSet[(filtration μ ν 𝓕 𝓖).predictable] ((Ioi t)×ˢ(Prod.snd ⁻¹' A))
    apply measurableSet_predictable_Ioi_prod
    change MeasurableSet[((IndependentNoiseProduct.filtration 𝓕 𝓖) t)⊔nullSigma μ ν] (Prod.snd ⁻¹' A)
    exact (le_sup_left:((IndependentNoiseProduct.filtration 𝓕 𝓖) t)≤((IndependentNoiseProduct.filtration 𝓕 𝓖) t)⊔nullSigma μ ν) _
      (@measurable_snd Ω Ξ (𝓕 t) (𝓖 t) A hA)

variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

theorem state_predictable(U:ℝ≥0→Ω→E)
    (hU:StronglyMeasurable[𝓕.predictable] (Function.uncurry U)):
    StronglyMeasurable[(filtration μ ν 𝓕 𝓖).predictable]
      (fun p:ℝ≥0×Space μ ν=>U p.1 p.2.1):=
  hU.comp_measurable (predictable_fst μ ν 𝓕 𝓖)

theorem state_law[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
    (H:ℝ≥0)(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω))
    (hU:Measurable (Function.uncurry U)):
    NativePathLawComparison.law H (measure μ ν) (fun t (z:Space μ ν)=>U t z.1) (fun z=>hc z.1)=
      NativePathLawComparison.law H μ U hc:=by
  apply Subtype.ext
  change (measure μ ν).map (NativeContinuousPath.path H (fun t (z:Space μ ν)=>U t z.1) (fun z=>hc z.1))=
    μ.map (NativeContinuousPath.path H U hc)
  have he:NativeContinuousPath.path H (fun t (z:Space μ ν)=>U t z.1) (fun z=>hc z.1)=
      (NativeContinuousPath.path H U hc)∘(Prod.fst:Space μ ν→Ω):=rfl
  rw [he,←Measure.map_map (NativeContinuousPath.measurable_path H U hc hU) (fst_measurable μ ν),
    (fst_preserving μ ν).map_eq]

end SHE.IndependentNoiseCompletion
