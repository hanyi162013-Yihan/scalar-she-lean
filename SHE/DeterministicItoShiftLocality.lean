module
public import SHE.DeterministicItoShiftBDG
public import SHE.StandardTerminalPastLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable{Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[SFinite μ]
variable(H v h:ℝ≥0)(hvh:v+h≤H)
include hvh

omit hvh in
theorem extend_event(s:ℝ≥0)(A:Set Ω)(f:ℝ≥0×Ω→C):
    extend v h ((eventAfter s A).indicator f)=
      (eventAfter (v+s) A).indicator (extend v h f):=by
  classical
  funext p
  by_cases hv:v<p.1
  · by_cases hu:p.1≤v+h
    · have he:relative v p∈eventAfter s A↔p∈eventAfter (v+s) A:=by
        change (s<p.1-v∧p.2∈A)↔(v+s<p.1∧p.2∈A)
        exact and_congr_left (fun _=>relative_order v s p.1 hv)
      simp only [extend,ite_eq_left hv,ite_eq_left hu,Set.indicator,he]
    · simp [Set.indicator,extend,hv,hu]
  · simp [Set.indicator,extend,hv]

theorem input_event(s:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[(filtration 𝓕 v) s] A)
    (f:Process (E:=C) (filtration 𝓕 v) μ h):
    input 𝓕 μ H v h hvh (eventProcess (filtration 𝓕 v) μ h s A hA f)=
      eventProcess 𝓕 μ H (v+s) A hA (input 𝓕 μ H v h hvh f):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  have he:=extend_ae 𝓕 μ H v h hvh
    (Lp.stronglyMeasurable (eventProcess (filtration 𝓕 v) μ h s A hA f)).measurable
    ((Lp.stronglyMeasurable f).indicator (eventAfter_measurable (filtration 𝓕 v) s hA)).measurable
    (eventProcess_ae (filtration 𝓕 v) μ h s A hA f)
  filter_upwards [input_ae 𝓕 μ H v h hvh (eventProcess (filtration 𝓕 v) μ h s A hA f),
    input_ae 𝓕 μ H v h hvh f,he,eventProcess_ae 𝓕 μ H (v+s) A hA (input 𝓕 μ H v h hvh f)]
    with p hi hf he ho
  rw [hi,he,ho,congrFun (extend_event (v:=v) (h:=h) s A f) p]
  by_cases ha:p∈eventAfter (v+s) A
  · rw [Set.indicator_of_mem ha,Set.indicator_of_mem ha,hf]
  · rw [Set.indicator_of_notMem ha,Set.indicator_of_notMem ha]

theorem input_post(s:ℝ≥0)(f:Process (E:=C) (filtration 𝓕 v) μ h):
    input 𝓕 μ H v h hvh (post (filtration 𝓕 v) μ h s f)=
      post 𝓕 μ H (v+s) (input 𝓕 μ H v h hvh f):=
  input_event 𝓕 μ H v h hvh s univ MeasurableSet.univ f

/-- Deterministic-past event pullout is preserved by the SAME
physical input extension, without a new locality premise. -/
theorem locality(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)
    (hlocal:StandardTerminalPastLocality J):
    StandardTerminalPastLocality (integral 𝓕 μ H v h hvh J):=by
  intro s A hA f
  have he:=hlocal (v+s) A hA (input 𝓕 μ H v h hvh f)
  rw [←input_event 𝓕 μ H v h hvh s A hA f,←input_post 𝓕 μ H v h hvh s f] at he
  exact he

omit [SFinite μ] hvh in
theorem nullComplete(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ):
    NullCompleteFiltration.ContainsNullSets (filtration 𝓕 v) μ:=by
  intro t A hA
  exact hnull (v+t) A hA

end SHE.DeterministicItoShift
