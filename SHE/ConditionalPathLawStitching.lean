module
public import Mathlib.Probability.Kernel.CondDistrib
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ConditionalPathLawStitching
open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
variable {Ω Ω' P F S:Type*}
variable[MeasurableSpace Ω][MeasurableSpace Ω'][MeasurableSpace P][MeasurableSpace F]
variable[StandardBorelSpace F][Nonempty F][MeasurableSpace S]
variable(μ:Measure Ω)(ν:Measure Ω')[IsFiniteMeasure μ][IsFiniteMeasure ν]
variable(X:Ω→P)(Y:Ω→F)(X':Ω'→P)(Y':Ω'→F)

/-- Equal prefix laws and equal genuine conditional future distributions
identify the full prefix/future joint laws. No Markov property or
conditional SPDE uniqueness is assumed or asserted here. -/
theorem joint (hX:AEMeasurable X μ)(hY:AEMeasurable Y μ)
    (hX':AEMeasurable X' ν)(hY':AEMeasurable Y' ν)
    (hprefix:μ.map X=ν.map X')
    (hfuture:condDistrib Y X μ=ᵐ[μ.map X] condDistrib Y' X' ν):
    μ.map (fun ω=>(X ω,Y ω))=ν.map (fun ω=>(X' ω,Y' ω)):=by
  calc
    _=(μ.map X) ⊗ₘ condDistrib Y X μ:=(compProd_map_condDistrib hX hY).symm
    _=(μ.map X) ⊗ₘ condDistrib Y' X' ν:=Measure.compProd_congr hfuture
    _=ν.map (fun ω=>(X' ω,Y' ω)):=by
      rw [hprefix,compProd_map_condDistrib hX' hY']

/-- Any measurable path concatenation preserves the checked joint-law
identity. Compatibility of actual path segments remains an ordinary
identity to be supplied by the restart construction. -/
theorem stitched (hX:Measurable X)(hY:Measurable Y)
    (hX':Measurable X')(hY':Measurable Y')
    (hprefix:μ.map X=ν.map X')
    (hfuture:condDistrib Y X μ=ᵐ[μ.map X] condDistrib Y' X' ν)
    (stitch:P×F→S)(hstitch:Measurable stitch):
    μ.map (fun ω=>stitch (X ω,Y ω))=
      ν.map (fun ω=>stitch (X' ω,Y' ω)):=by
  have he:=congrArg (fun m:Measure (P×F)=>m.map stitch)
    (joint μ ν X Y X' Y' hX.aemeasurable hY.aemeasurable hX'.aemeasurable hY'.aemeasurable hprefix hfuture)
  rw [Measure.map_map hstitch (hX.prodMk hY),Measure.map_map hstitch (hX'.prodMk hY')] at he
  exact he

/-- Actual full paths inherit equality of laws once their prefix/future
reconstruction and the true conditional future-kernel equality are
proved. This is measure-theoretic stitching, not a restart axiom. -/
theorem reconstructed (hX:Measurable X)(hY:Measurable Y)
    (hX':Measurable X')(hY':Measurable Y')
    (hprefix:μ.map X=ν.map X')
    (hfuture:condDistrib Y X μ=ᵐ[μ.map X] condDistrib Y' X' ν)
    (stitch:P×F→S)(hstitch:Measurable stitch)
    (U:Ω→S)(U':Ω'→S)
    (hU:U=ᵐ[μ] fun ω=>stitch (X ω,Y ω))
    (hU':U'=ᵐ[ν] fun ω=>stitch (X' ω,Y' ω)):
    μ.map U=ν.map U':=by
  calc
    _=μ.map (fun ω=>stitch (X ω,Y ω)):=Measure.map_congr hU
    _=ν.map (fun ω=>stitch (X' ω,Y' ω)):=
      stitched μ ν X Y X' Y' hX hY hX' hY' hprefix hfuture stitch hstitch
    _=ν.map U':=Measure.map_congr hU'.symm
end SHE.ConditionalPathLawStitching
