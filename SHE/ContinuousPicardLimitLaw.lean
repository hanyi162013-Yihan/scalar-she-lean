module
public import SHE.ContinuousPathCylindricalLaw
public import SHE.NativePathLawComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.ContinuousPicardLimitLaw
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
variable {Ω Ω' E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(H:ℝ≥0)(hH:0<H)(μ:Measure Ω)(ν:Measure Ω')[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
variable(U:ℝ≥0→Ω→E)(V:ℝ≥0→Ω'→E)
variable(hc:∀ω,Continuous (fun t=>U t ω))(hd:∀ω,Continuous (fun t=>V t ω))
variable(hU:Measurable (Function.uncurry U))(hV:Measurable (Function.uncurry V))
variable(X:ℕ→ℝ≥0→Ω→E)(Y:ℕ→ℝ≥0→Ω'→E)
variable(hxc:∀n ω,Continuous (fun t=>X n t ω))(hyc:∀n ω,Continuous (fun t=>Y n t ω))
variable(hxm:∀n,Measurable (Function.uncurry (X n)))(hym:∀n,Measurable (Function.uncurry (Y n)))
local instance : MeasurableSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))):=borel _
local instance : BorelSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))):=⟨rfl⟩

include hH hU hV hxc hyc hxm hym in
/-- Common cylindrical laws of actual continuous Picard approximants,
combined with their ordinary product-L2 limits, determine the actual
continuous solution laws. This supplies no SPDE-law input. -/
theorem paths
    (hlaw:∀n,μ.map (fun ω=>fun t=>X n t ω)=ν.map (fun ω=>fun t=>Y n t ω))
    (hi:∀n,Integrable (fun p:ℝ≥0×Ω=>‖U p.1 p.2-X n p.1 p.2‖^2) (PredictableL2.energyMeasure μ H))
    (hj:∀n,Integrable (fun p:ℝ≥0×Ω'=>‖V p.1 p.2-Y n p.1 p.2‖^2) (PredictableL2.energyMeasure ν H))
    (he:Tendsto (fun n=>∫p:ℝ≥0×Ω,‖U p.1 p.2-X n p.1 p.2‖^2 ∂PredictableL2.energyMeasure μ H) atTop (𝓝 0))
    (hf:Tendsto (fun n=>∫p:ℝ≥0×Ω',‖V p.1 p.2-Y n p.1 p.2‖^2 ∂PredictableL2.energyMeasure ν H) atTop (𝓝 0)):
    NativePathLawComparison.law H μ U hc=NativePathLawComparison.law H ν V hd:=by
  let canonical:ℕ→ProbabilityMeasure (Lp E 2 (SHE.timeMeasure (H:ℝ))):=fun n=>
    ProbabilityMeasure.map (⟨μ,inferInstance⟩:ProbabilityMeasure Ω)
      (NativeContinuousPath.integrated H (X n) (hxc n))
  apply NativePathLawComparison.laws_eq H hH μ ν U V hc hd hU hV X Y hxc hyc hxm hym
    hi hj he hf canonical (fun _=>0) (fun _=>0) (fun _=>le_rfl) (fun _=>le_rfl)
    tendsto_const_nhds tendsto_const_nhds
  · intro n f
    change |(∫ω,f (NativeContinuousPath.integrated H (X n) (hxc n) ω) ∂μ)-
      (∫x,f x ∂μ.map (NativeContinuousPath.integrated H (X n) (hxc n)))|≤_
    rw [integral_map (NativeContinuousPath.measurable_integrated H (X n) (hxc n) (hxm n)).aemeasurable
      f.continuous.aestronglyMeasurable]
    simp
  · intro n f
    have hh:=ContinuousPathCylindricalLaw.integrated H μ ν (X n) (Y n) (hxc n) (hyc n) (hxm n) (hym n) (hlaw n)
    change |(∫ω,f (NativeContinuousPath.integrated H (Y n) (hyc n) ω) ∂ν)-
      (∫x,f x ∂μ.map (NativeContinuousPath.integrated H (X n) (hxc n)))|≤_
    rw [hh,integral_map (NativeContinuousPath.measurable_integrated H (Y n) (hyc n) (hym n)).aemeasurable
      f.continuous.aestronglyMeasurable]
    simp
end SHE.ContinuousPicardLimitLaw
