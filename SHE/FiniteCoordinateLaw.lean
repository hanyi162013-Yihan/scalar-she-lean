module
public import Mathlib.Probability.Process.FiniteDimensionalLaws
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.FiniteCoordinateLaw
open MeasureTheory ProbabilityTheory
variable {Ω Ω' T E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω'][MeasurableSpace E]

/-- Finite coordinate laws determine the full cylindrical driver law,
including for processes living on DIFFERENT original probability spaces.
This is a proved projective-measure argument, not stochastic input. -/
theorem map_eq (μ:Measure Ω)(ν:Measure Ω')[IsFiniteMeasure μ][IsFiniteMeasure ν]
    (X:T→Ω→E)(Y:T→Ω'→E)(hX:∀t,Measurable (X t))(hY:∀t,Measurable (Y t))
    (hf:∀(n:ℕ)(a:Fin n→T),
      μ.map (fun ω=>fun i:Fin n=>X (a i) ω)=ν.map (fun ω=>fun i:Fin n=>Y (a i) ω)):
    μ.map (fun ω=>fun t=>X t ω)=ν.map (fun ω=>fun t=>Y t ω):=by
  classical
  have hx:Measurable (fun ω=>fun t=>X t ω):=measurable_pi_iff.mpr hX
  have hy:Measurable (fun ω=>fun t=>Y t ω):=measurable_pi_iff.mpr hY
  have hpx:=isProjectiveLimit_map (P:=μ) hx.aemeasurable
  have hpy:=isProjectiveLimit_map (P:=ν) hy.aemeasurable
  have he:∀I:Finset T,μ.map (fun ω=>I.restrict (fun t=>X t ω))=
      ν.map (fun ω=>I.restrict (fun t=>Y t ω)):=by
    intro I
    let e:I≃Fin (Fintype.card I):=Fintype.equivFin I
    let a:Fin (Fintype.card I)→T:=fun j=>(e.symm j).1
    let decode:(Fin (Fintype.card I)→E)→(I→E):=fun z i=>z (e i)
    have hd:Measurable decode:=measurable_pi_iff.mpr (fun i=>measurable_pi_apply (e i))
    have hh:=congrArg (fun P:Measure (Fin (Fintype.card I)→E)=>P.map decode) (hf (Fintype.card I) a)
    rw [Measure.map_map hd (measurable_pi_iff.mpr (fun j=>hX (a j))),
      Measure.map_map hd (measurable_pi_iff.mpr (fun j=>hY (a j)))] at hh
    convert! hh using 1 <;> congr 1 <;> funext ω i <;> simp only [decode,a,Function.comp_def,Equiv.symm_apply_apply,Finset.restrict_def]
  simp_rw [he] at hpx
  exact hpx.unique hpy
end SHE.FiniteCoordinateLaw
