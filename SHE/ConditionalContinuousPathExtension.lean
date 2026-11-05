module
public import SHE.ContinuousPathRestriction
public import SHE.ConditionalPathLawStitching
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ConditionalContinuousPathExtension
open Set MeasureTheory ProbabilityTheory ContinuousPathRestriction
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
local instance pathNonempty {E:Type*}[TopologicalSpace E][Nonempty E](H:ℝ≥0):Nonempty C(Interval H,E):=
  ⟨ContinuousMap.const _ (Classical.choice (inferInstance:Nonempty E))⟩
section Metric
variable {Ω Ω' E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable [MetricSpace E][CompleteSpace E][SecondCountableTopology E]
  [MeasurableSpace E][BorelSpace E][Nonempty E]
variable (v h:ℝ≥0)(μ:Measure Ω)(ν:Measure Ω')
variable (U:Ω→C(Interval (v+h),E))(V:Ω'→C(Interval (v+h),E))

/-- Equality of the genuine restriction-pair laws identifies the full
continuous-path laws, with no measurable stitch or compatibility premise. -/
theorem of_joint (hU:Measurable U)(hV:Measurable V)
    (hjoint:μ.map (fun ω=>split v h (U ω))=ν.map (fun ω=>split v h (V ω))):
    μ.map U=ν.map V:=by
  apply ContinuousPathRestriction.map_injective v h
  rw [Measure.map_map (continuous_split v h).measurable hU,
    Measure.map_map (continuous_split v h).measurable hV]
  exact hjoint

/-- Two-interval law extension from equal actual prefix laws and equal
actual conditional future kernels. This is only measure theory and
continuous-path geometry; no SPDE or Markov property is an assumption. -/
theorem of_conditional [IsFiniteMeasure μ][IsFiniteMeasure ν]
    (hU:Measurable U)(hV:Measurable V)
    (hprefix:μ.map (fun ω=>past v h (U ω))=ν.map (fun ω=>past v h (V ω)))
    (hfuture:condDistrib (fun ω=>future v h (U ω)) (fun ω=>past v h (U ω)) μ
      =ᵐ[μ.map (fun ω=>past v h (U ω))]
      condDistrib (fun ω=>future v h (V ω)) (fun ω=>past v h (V ω)) ν):
    μ.map U=ν.map V:=by
  apply of_joint v h μ ν U V hU hV
  exact ConditionalPathLawStitching.joint μ ν
    (fun ω=>past v h (U ω)) (fun ω=>future v h (U ω))
    (fun ω=>past v h (V ω)) (fun ω=>future v h (V ω))
    ((continuous_past v h).measurable.comp hU).aemeasurable
    ((continuous_future v h).measurable.comp hU).aemeasurable
    ((continuous_past v h).measurable.comp hV).aemeasurable
    ((continuous_future v h).measurable.comp hV).aemeasurable hprefix hfuture

end Metric
section Hilbert
variable {Ω Ω' E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (v h:ℝ≥0)(μ:Measure Ω)(ν:Measure Ω')
/-- The same extension applied directly to the actual path random
variables constructed from continuous, jointly measurable processes. -/
theorem processes [IsFiniteMeasure μ][IsFiniteMeasure ν]
    (X:ℝ≥0→Ω→E)(Y:ℝ≥0→Ω'→E)
    (hc:∀ω,Continuous (fun t=>X t ω))(hd:∀ω,Continuous (fun t=>Y t ω))
    (hX:Measurable (Function.uncurry X))(hY:Measurable (Function.uncurry Y))
    (hprefix:μ.map (fun ω=>past v h (NativeContinuousPath.path (v+h) X hc ω))=
      ν.map (fun ω=>past v h (NativeContinuousPath.path (v+h) Y hd ω)))
    (hfuture:condDistrib
      (fun ω=>future v h (NativeContinuousPath.path (v+h) X hc ω))
      (fun ω=>past v h (NativeContinuousPath.path (v+h) X hc ω)) μ
      =ᵐ[μ.map (fun ω=>past v h (NativeContinuousPath.path (v+h) X hc ω))]
      condDistrib
      (fun ω=>future v h (NativeContinuousPath.path (v+h) Y hd ω))
      (fun ω=>past v h (NativeContinuousPath.path (v+h) Y hd ω)) ν):
    μ.map (NativeContinuousPath.path (v+h) X hc)=
      ν.map (NativeContinuousPath.path (v+h) Y hd):=
  of_conditional v h μ ν _ _ (NativeContinuousPath.measurable_path (v+h) X hc hX)
    (NativeContinuousPath.measurable_path (v+h) Y hd hY) hprefix hfuture
end Hilbert
end SHE.ConditionalContinuousPathExtension
