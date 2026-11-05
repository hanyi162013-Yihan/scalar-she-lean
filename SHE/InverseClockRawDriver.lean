module
public import SHE.RawCylindricalCoordinates
public import SHE.TimeDilationInverseIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
namespace SHE.InverseClockRawDriver
open MeasureTheory PredictableL2 PredictableTimeDilation StoppedItoInputs Set
open scoped NNReal ENNReal
variable{Ω Ω' C ι:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[Countable ι][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(c:ℝ≥0)(hc:0<c)(h:ℝ≥0)(e:ι→C)
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) (filtration 𝓕 (clock c hc)) μ (c*h))
local notation "FU"=>𝓕
local notation "FN"=>filtration 𝓕 (clock c hc)

theorem input (i:ι)(t:ℝ≥0):
    (processEquivalence 𝓕 μ c hc h).symm
      (stop 𝓕 μ h t (RawCylindricalCoordinates.row 𝓕 μ h e i))=
    (Real.sqrt (c:ℝ)⁻¹) • stop FN μ (c*h) (clock c hc t)
      (RawCylindricalCoordinates.row FN μ (c*h) e i):=by
  let R:=RawCylindricalCoordinates.row 𝓕 μ h e i
  let RN:=RawCylindricalCoordinates.row FN μ (c*h) e i
  have hu:∀ᵐp∂energyMeasure μ h,stop 𝓕 μ h t R p=
      (before (Ω:=Ω) t).indicator (fun _=>e i) p:=by
    filter_upwards [stop_ae 𝓕 μ h t R,RotatedCylindricalCoordinates.constant_ae 𝓕 μ h (e i)] with p hp hr
    change R p=e i at hr
    rw [hp]
    by_cases hin:p∈before (Ω:=Ω) t
    · rw [indicator_of_mem hin,indicator_of_mem hin,hr]
    · rw [indicator_of_notMem hin,indicator_of_notMem hin]
  have hrev:=ScaledLpPull.inverse_preserving (energyMeasure μ h) (energyMeasure μ (c*h))
    (c:ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc h μ)
  have hp:∀ᵐp∂energyMeasure μ (c*h),stop 𝓕 μ h t R ((clock c hc).symm p.1,p.2)=
      (before (Ω:=Ω) t).indicator (fun _=>e i) ((clock c hc).symm p.1,p.2):=
    ScaledLpPull.ae_comp (energyMeasure μ (c*h)) (energyMeasure μ h) (c:ℝ)⁻¹
      (inv_pos.mpr (show (0:ℝ)<c from hc)) (ambientEquiv c hc).symm hrev hu
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [processEquivalence_symm_ae 𝓕 μ c hc h (stop 𝓕 μ h t R),hp,
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.sqrt (c:ℝ)⁻¹) (stop FN μ (c*h) (clock c hc t) RN)),
    stop_ae FN μ (c*h) (clock c hc t) RN,
    RotatedCylindricalCoordinates.constant_ae FN μ (c*h) (e i)] with p hs hp hm ht hr
  change RN p=e i at hr
  rw [hs,hp,hm]
  simp only [Pi.smul_apply]
  rw [ht]
  have hi:((clock c hc).symm p.1,p.2)∈before (Ω:=Ω) t ↔ p∈before (Ω:=Ω) (clock c hc t):=by
    change ((clock c hc).symm p.1:ℝ)<(t:ℝ) ↔ (p.1:ℝ)<(clock c hc t:ℝ)
    have hh:((clock c hc).symm p.1<t ↔ p.1<clock c hc t):=by
      simpa only [OrderIso.symm_apply_apply] using
        ((clock c hc).symm.lt_iff_lt (x:=p.1) (y:=clock c hc t))
    exact_mod_cast hh
  by_cases hin:p∈before (Ω:=Ω) (clock c hc t)
  · rw [indicator_of_mem (hi.mpr hin),indicator_of_mem hin,hr]
  · rw [indicator_of_notMem (fun h=>hin (hi.mp h)),indicator_of_notMem hin]

/-- Exact rescaling of the SAME original stopped raw coordinates. -/
theorem value (i:ι)(t:ℝ≥0):
    RawCylindricalCoordinates.value 𝓕 μ h e (inverseIntegral 𝓕 μ c hc h J) i t=ᵐ[μ]
      (fun ω=>(Real.sqrt (c:ℝ)⁻¹)*
        RawCylindricalCoordinates.value FN μ (c*h) e J i (clock c hc t) ω):=by
  change (fun ω=>J.integral ((processEquivalence 𝓕 μ c hc h).symm
    (stop 𝓕 μ h t (RawCylindricalCoordinates.row 𝓕 μ h e i))) ω)=ᵐ[μ] _
  rw [input 𝓕 μ c hc h e i t,map_smul]
  exact (Lp.coeFn_smul (Real.sqrt (c:ℝ)⁻¹) (J.integral
    (stop FN μ (c*h) (clock c hc t) (RawCylindricalCoordinates.row FN μ (c*h) e i)))).mono
      (fun _ h=>by simpa only [Pi.smul_apply,smul_eq_mul,RawCylindricalCoordinates.value] using h)
end SHE.InverseClockRawDriver

namespace SHE.InverseClockRawDriver
open MeasureTheory PredictableL2 PredictableTimeDilation
open scoped NNReal ENNReal
variable{Ω Ω' C ι:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[Countable ι][DecidableEq ι]
/-- Full raw driver laws remain equal under the literal inverse
Brownian clock. Only finite-coordinate AE identities are used. -/
theorem map_eq
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (c:ℝ≥0)(hc:0<c)(h:ℝ≥0)(e:ι→C)
    (J:StandardTerminalIto (C:=C) (E:=ℝ) (filtration 𝓕 (clock c hc)) μ (c*h))
    (K:StandardTerminalIto (C:=C) (E:=ℝ) (filtration 𝓖 (clock c hc)) ν (c*h))
    (he:μ.map (fun ω=>fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value (filtration 𝓕 (clock c hc)) μ (c*h) e J p.1 p.2 ω)=
      ν.map (fun ω=>fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value (filtration 𝓖 (clock c hc)) ν (c*h) e K p.1 p.2 ω)):
    μ.map (fun ω=>fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value 𝓕 μ h e (inverseIntegral 𝓕 μ c hc h J) p.1 p.2 ω)=
      ν.map (fun ω=>fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value 𝓖 ν h e (inverseIntegral 𝓖 ν c hc h K) p.1 p.2 ω):=by
  apply FiniteCoordinateLaw.map_eq μ ν
    (fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value 𝓕 μ h e (inverseIntegral 𝓕 μ c hc h J) p.1 p.2)
    (fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value 𝓖 ν h e (inverseIntegral 𝓖 ν c hc h K) p.1 p.2)
    (fun p=>RawCylindricalCoordinates.value_measurable 𝓕 μ h e _ p.1 p.2)
    (fun p=>RawCylindricalCoordinates.value_measurable 𝓖 ν h e _ p.1 p.2)
  intro n a
  let decode:((ι×ℝ≥0)→ℝ)→(Fin n→ℝ):=fun x i=>(Real.sqrt (c:ℝ)⁻¹)*x ((a i).1,clock c hc (a i).2)
  have hd:Measurable decode:=measurable_pi_iff.mpr (fun i=>measurable_const.mul (measurable_pi_apply _))
  have hh:=congrArg (fun m:Measure ((ι×ℝ≥0)→ℝ)=>m.map decode) he
  rw [Measure.map_map hd (measurable_pi_iff.mpr (fun p=>RawCylindricalCoordinates.value_measurable _ μ (c*h) e J p.1 p.2)),
    Measure.map_map hd (measurable_pi_iff.mpr (fun p=>RawCylindricalCoordinates.value_measurable _ ν (c*h) e K p.1 p.2))] at hh
  calc
    _=μ.map (decode ∘ (fun ω=>fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value (filtration 𝓕 (clock c hc)) μ (c*h) e J p.1 p.2 ω)):=by
      apply Measure.map_congr
      filter_upwards [ae_all_iff.mpr (fun i:Fin n=>value 𝓕 μ c hc h e J (a i).1 (a i).2)] with ω hω
      exact funext hω
    _=ν.map (decode ∘ (fun ω=>fun p:ι×ℝ≥0=>RawCylindricalCoordinates.value (filtration 𝓖 (clock c hc)) ν (c*h) e K p.1 p.2 ω)):=hh
    _=_:=by
      symm
      apply Measure.map_congr
      filter_upwards [ae_all_iff.mpr (fun i:Fin n=>value 𝓖 ν c hc h e K (a i).1 (a i).2)] with ω hω
      exact funext hω
end SHE.InverseClockRawDriver
