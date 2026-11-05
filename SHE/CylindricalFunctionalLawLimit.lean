module
public import SHE.FiniteJointProbabilityLimit
public import SHE.FiniteCoordinateLaw
public import SHE.CommonLawLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.CylindricalFunctionalLawLimit
open MeasureTheory Filter
open scoped Topology
variable {Ω Ω' S T E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω'][MeasurableSpace S]
variable [NormedAddCommGroup E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

/-- Actual finite measurable functionals with a common source law
transfer all dependent cylindrical coordinates through probability
limits. This pure law-limit theorem adds no stochastic hypothesis. -/
theorem law(μ:Measure Ω)(ν:Measure Ω')[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
    (A:Ω→S)(B:Ω'→S)(hA:Measurable A)(hB:Measurable B)(hLaw:μ.map A=ν.map B)
    (φ:ℕ→T→S→E)(hφ:∀n t,Measurable (φ n t))
    (X:T→Ω→E)(Y:T→Ω'→E)(hX:∀t,Measurable (X t))(hY:∀t,Measurable (Y t))
    (hx:∀t,TendstoInMeasure μ (fun n ω=>φ n t (A ω)) atTop (X t))
    (hy:∀t,TendstoInMeasure ν (fun n ω=>φ n t (B ω)) atTop (Y t)):
    μ.map (fun ω=>fun t=>X t ω)=ν.map (fun ω=>fun t=>Y t ω):=by
  apply FiniteCoordinateLaw.map_eq μ ν X Y hX hY
  intro m a
  let f:ℕ→Ω→Fin m→E:=fun n ω i=>φ n (a i) (A ω)
  let g:ℕ→Ω'→Fin m→E:=fun n ω i=>φ n (a i) (B ω)
  have hf(n:ℕ)(i:Fin m):Measurable (fun ω=>f n ω i):=(hφ n (a i)).comp hA
  have hg(n:ℕ)(i:Fin m):Measurable (fun ω=>g n ω i):=(hφ n (a i)).comp hB
  apply CommonLawLimit.map_eq μ ν f g _ _
    (fun n=>(measurable_pi_iff.mpr (hf n)).aemeasurable)
    (fun n=>(measurable_pi_iff.mpr (hg n)).aemeasurable)
    (FiniteJointProbabilityLimit.fin μ m f _ hf (fun i=>hx (a i)))
    (FiniteJointProbabilityLimit.fin ν m g _ hg (fun i=>hy (a i)))
  intro n
  have hm:Measurable (fun s:S=>fun i:Fin m=>φ n (a i) s):=
    measurable_pi_iff.mpr (fun i=>hφ n (a i))
  have h:=congrArg (fun P:Measure S=>P.map (fun s:S=>fun i:Fin m=>φ n (a i) s)) hLaw
  rw [Measure.map_map hm hA,Measure.map_map hm hB] at h
  exact h
end SHE.CylindricalFunctionalLawLimit
