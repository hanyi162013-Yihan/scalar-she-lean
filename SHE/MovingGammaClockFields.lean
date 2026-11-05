module
public import SHE.NativeGammaDamping
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.MovingGammaClockFields
open Set MeasureTheory PredictableL2
open scoped NNReal
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(past terminal:ℝ→ℝ≥0)
variable (hpast:Measurable past)(hterminal:Measurable terminal)
def window:Set (ℝ×(ℝ≥0×Ω)):=
  {z|past z.1<z.2.1∧z.2.1<terminal z.1}
include hpast hterminal in
theorem window_predictable:
    MeasurableSet[((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable)] (window past terminal):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have ht:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  exact (measurableSet_lt (NNReal.continuous_coe.measurable.comp (hpast.comp measurable_fst)) ht).inter
    (measurableSet_lt ht (NNReal.continuous_coe.measurable.comp (hterminal.comp measurable_fst)))
def age (z:ℝ×(ℝ≥0×Ω)):ℝ:=NativeGammaClock.age (past z.1) (terminal z.1) z.2
include hpast hterminal in
theorem age_predictable:
    @Measurable _ ℝ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ (age past terminal):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have ht:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  exact ((NNReal.continuous_coe.measurable.comp (hterminal.comp measurable_fst)).sub ht).ite
    (window_predictable 𝓕 past terminal hpast hterminal) measurable_const
def damping (Λ:ℝ)(z:ℝ×(ℝ≥0×Ω)):ℝ:=
  NativeGammaDamping.value Λ (past z.1) (terminal z.1) z.2
include hpast hterminal in
theorem damping_predictable (Λ:ℝ):
    @Measurable _ ℝ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ (damping past terminal Λ):=
  (((age_predictable 𝓕 past terminal hpast hterminal).const_mul (-Λ)).exp)
theorem damping_bounds {Λ:ℝ}(hΛ:0≤Λ)(z:ℝ×(ℝ≥0×Ω)):
    0≤damping past terminal Λ z∧damping past terminal Λ z≤1:=
  ⟨NativeGammaDamping.nonneg _ _ _ _,NativeGammaDamping.le_one _ _ _ hΛ _⟩
end SHE.MovingGammaClockFields
