module
public import SHE.StandardTerminalPastLocality
public import SHE.PastItoAlgebra
public import SHE.TimeDilationInverseIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.InverseClockLocality
open MeasureTheory PredictableL2 PredictableTimeDilation PastItoInputs Set
open scoped NNReal ENNReal
variable{Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[SFinite μ]
variable(c:ℝ≥0)(hc:0<c)(h:ℝ≥0)
local notation "FN"=>filtration 𝓕 (clock c hc)

theorem event_measurable (v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A):
    MeasurableSet[FN (clock c hc v)] A:=by
  change MeasurableSet[𝓕 ((clock c hc).symm (clock c hc v))] A
  exact (congrArg (fun s:ℝ≥0=>MeasurableSet[𝓕 s] A) ((clock c hc).symm_apply_apply v)).mpr hA

/-- The inverse clock carries exactly the same past-event restriction,
including the Brownian square-root Jacobian. -/
theorem event_input (v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A)
    (u:Process (E:=C) 𝓕 μ h):
    (processEquivalence 𝓕 μ c hc h).symm (eventProcess 𝓕 μ h v A hA u)=
      eventProcess FN μ (c*h) (clock c hc v) A (event_measurable 𝓕 c hc v A hA)
        ((processEquivalence 𝓕 μ c hc h).symm u):=by
  have hrev:=ScaledLpPull.inverse_preserving (energyMeasure μ h) (energyMeasure μ (c*h))
    (c:ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc h μ)
  have hp:∀ᵐp∂energyMeasure μ (c*h),
      eventProcess 𝓕 μ h v A hA u ((clock c hc).symm p.1,p.2)=
      (eventAfter v A).indicator u ((clock c hc).symm p.1,p.2):=
    ScaledLpPull.ae_comp (energyMeasure μ (c*h)) (energyMeasure μ h) (c:ℝ)⁻¹
      (inv_pos.mpr (show (0:ℝ)<c from hc)) (ambientEquiv c hc).symm hrev
        (eventProcess_ae 𝓕 μ h v A hA u)
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [processEquivalence_symm_ae 𝓕 μ c hc h (eventProcess 𝓕 μ h v A hA u),
    hp,processEquivalence_symm_ae 𝓕 μ c hc h u,
    eventProcess_ae FN μ (c*h) (clock c hc v) A (event_measurable 𝓕 c hc v A hA)
      ((processEquivalence 𝓕 μ c hc h).symm u)] with p he hp hu ho
  rw [he,hp,ho]
  have hi:((clock c hc).symm p.1,p.2)∈eventAfter v A ↔p∈eventAfter (clock c hc v) A:=by
    change (v<(clock c hc).symm p.1 ∧p.2∈A)↔(clock c hc v<p.1 ∧p.2∈A)
    have ht:(v<(clock c hc).symm p.1 ↔clock c hc v<p.1):=by
      constructor
      · intro hh
        simpa only [OrderIso.apply_symm_apply] using (clock c hc).strictMono hh
      · intro hh
        simpa only [OrderIso.symm_apply_apply] using (clock c hc).symm.strictMono hh
    rw [ht]
  by_cases hin:p∈eventAfter (clock c hc v) A
  · rw [indicator_of_mem (hi.mpr hin),indicator_of_mem hin,hu]
  · rw [indicator_of_notMem (fun hh=>hin (hi.mp hh)),indicator_of_notMem hin,smul_zero]

/-- Ordinary full-horizon locality is preserved by the SAME inverse
Itô clock. It is proved from the actual input equivalence. -/
theorem locality
    (J:StandardTerminalIto (C:=C) (E:=E) FN μ (c*h))
    (hlocal:StandardTerminalPastLocality J):
    StandardTerminalPastLocality (inverseIntegral 𝓕 μ c hc h J):=by
  intro v A hA u
  have hh:=hlocal (clock c hc v) A (event_measurable 𝓕 c hc v A hA)
    ((processEquivalence 𝓕 μ c hc h).symm u)
  rw [←event_input 𝓕 μ c hc h v A hA u] at hh
  have hp:(processEquivalence 𝓕 μ c hc h).symm (post 𝓕 μ h v u)=
      post FN μ (c*h) (clock c hc v) ((processEquivalence 𝓕 μ c hc h).symm u):=
    event_input 𝓕 μ c hc h v univ MeasurableSet.univ u
  rw [←hp] at hh
  exact hh

/-- Null completeness passes to the unit clock without a new
filtration assumption. -/
theorem null_complete (hn:NullCompleteFiltration.ContainsNullSets FN μ):
    NullCompleteFiltration.ContainsNullSets 𝓕 μ:=by
  intro v A hA
  have hh:=hn (clock c hc v) A hA
  change MeasurableSet[𝓕 ((clock c hc).symm (clock c hc v))] A at hh
  exact (congrArg (fun s:ℝ≥0=>MeasurableSet[𝓕 s] A) ((clock c hc).symm_apply_apply v)).mp hh
end SHE.InverseClockLocality
