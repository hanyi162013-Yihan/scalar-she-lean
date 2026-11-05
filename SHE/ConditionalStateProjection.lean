module
public import SHE.ConditionalPathLawStitching
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ConditionalStateProjection
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory
variable {Ω P W S:Type*}[MeasurableSpace Ω][MeasurableSpace P]
  [MeasurableSpace W][StandardBorelSpace W][Nonempty W]
  [MeasurableSpace S][StandardBorelSpace S][Nonempty S]
variable(μ:Measure Ω)[IsFiniteMeasure μ](X:Ω→P)(Y:Ω→W)

/-- Project a conditional future weak model to its state path. Equality
of projected future STATE kernels suffices; no joint state/noise law
comparison is introduced. -/
theorem projection(hX:AEMeasurable X μ)(hY:AEMeasurable Y μ)
    (state:W→S)(hs:Measurable state):
    condDistrib (fun ω=>state (Y ω)) X μ=ᵐ[μ.map X] (condDistrib Y X μ).map state:=
  condDistrib_comp hX hY hs

variable {R:Type*}[MeasurableSpace R][StandardBorelSpace R][Nonempty R]
/-- In particular an actual conditional (future-state,future-driver)
model projects to its true future-state conditional distribution. -/
theorem state_fst(X:Ω→P)(Y:Ω→S×R)(hX:AEMeasurable X μ)(hY:AEMeasurable Y μ):
    condDistrib (fun ω=>(Y ω).1) X μ=ᵐ[μ.map X] (condDistrib Y X μ).map Prod.fst:=
  condDistrib_comp hX hY measurable_fst
end SHE.ConditionalStateProjection
