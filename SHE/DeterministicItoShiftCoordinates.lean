module
public import SHE.DeterministicItoShiftIntegral
public import SHE.AllHorizonCylindricalCoordinates
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.DeterministicItoShiftCoordinates
open MeasureTheory ProbabilityTheory PredictableL2 StoppedItoInputs Set DeterministicItoShift
open scoped NNReal ENNReal
variable{Ω C ι:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(H v h:ℝ≥0)(hvh:v+h≤H)(e:ι→C)

/-- The actual shifted stopped constant row is EXACTLY the difference
of the SAME original global stopped rows. -/
theorem input(i:ι)(t:ℝ≥0)(ht:t≤h):
    DeterministicItoShift.input 𝓕 μ H v h hvh
      (stop (filtration 𝓕 v) μ h t (RawCylindricalCoordinates.row (filtration 𝓕 v) μ h e i))=
    stop 𝓕 μ H (v+t) (RawCylindricalCoordinates.row 𝓕 μ H e i)-
      stop 𝓕 μ H v (RawCylindricalCoordinates.row 𝓕 μ H e i):=by
  let f:=stop (filtration 𝓕 v) μ h t (RawCylindricalCoordinates.row (filtration 𝓕 v) μ h e i)
  let g:ℝ≥0×Ω→C:=(before (Ω:=Ω) t).indicator (fun _=>e i)
  have hfg:f=ᵐ[energyMeasure μ h] g:=by
    filter_upwards[stop_ae (filtration 𝓕 v) μ h t
      (RawCylindricalCoordinates.row (filtration 𝓕 v) μ h e i),
      RotatedCylindricalCoordinates.constant_ae (filtration 𝓕 v) μ h (e i)] with p hp hc
    rw[hp]
    by_cases hin:p∈before (Ω:=Ω) t
    · simpa only[g,indicator_of_mem hin,RawCylindricalCoordinates.row] using hc
    · simp only[g,indicator_of_notMem hin]
  have he:=extend_ae 𝓕 μ H v h hvh (Lp.stronglyMeasurable f).measurable
    (measurable_const.indicator (before_measurable (filtration 𝓕 v) t)) hfg
  have hv:∀ᵐp∂energyMeasure μ H,p.1≠v:=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne v)
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards[input_ae 𝓕 μ H v h hvh f,he,hv,
    stop_ae 𝓕 μ H (v+t) (RawCylindricalCoordinates.row 𝓕 μ H e i),
    stop_ae 𝓕 μ H v (RawCylindricalCoordinates.row 𝓕 μ H e i),
    RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (e i),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub
      (stop 𝓕 μ H (v+t) (RawCylindricalCoordinates.row 𝓕 μ H e i))
      (stop 𝓕 μ H v (RawCylindricalCoordinates.row 𝓕 μ H e i)))] with p hi he hv h1 h0 hc hs
  rw[hi,he,hs]
  simp only[Pi.sub_apply]
  rw[h1,h0]
  change RawCylindricalCoordinates.row 𝓕 μ H e i p=e i at hc
  change DeterministicItoShift.extend v h g p=(before (v+t)).indicator _ p-(before v).indicator _ p
  by_cases hp:v<p.1
  · have hn:¬(p.1:ℝ)<(v:ℝ):=not_lt.mpr (by exact_mod_cast hp.le)
    have hh:((p.1-v:ℝ≥0):ℝ)=(p.1:ℝ)-(v:ℝ):=NNReal.coe_sub hp.le
    have hlt:((p.1-v:ℝ≥0):ℝ)<(t:ℝ)↔(p.1:ℝ)<(v+t:ℝ≥0):=by
      rw[hh,NNReal.coe_add]
      constructor <;> intro hlt <;> linarith
    by_cases hu:p.1≤v+h
    · have hlt':((p.1-v:ℝ≥0):ℝ)<(t:ℝ)↔(p.1:ℝ)<(v:ℝ)+(t:ℝ):=by
        simpa only[NNReal.coe_add] using hlt
      have hltN:p.1-v<t↔p.1<v+t:=by exact_mod_cast hlt
      have hnN:¬p.1<v:=not_lt.mpr hp.le
      simp[DeterministicItoShift.extend,hp,hu,g,relative,before,Set.indicator_apply,Set.mem_setOf_eq,hlt',hltN,hn,hnN,hc,←NNReal.coe_add]

    · have hl:¬(p.1:ℝ)<(v+t:ℝ≥0):=by
        have ht':v+t≤v+h:=add_le_add_right ht v
        have hpu:v+h<p.1:=lt_of_not_ge hu
        exact not_lt.mpr (by exact_mod_cast ht'.trans hpu.le)
      have hlN:¬p.1<v+t:=by exact_mod_cast hl
      have hnN:¬p.1<v:=not_lt.mpr hp.le
      simp[DeterministicItoShift.extend,hp,hu,before,Set.indicator_apply,Set.mem_setOf_eq,hn,hl,hlN,hnN,←NNReal.coe_add]
  · have hq:p.1<v:=lt_of_le_of_ne (le_of_not_gt hp) hv
    have hl:(p.1:ℝ)<(v+t:ℝ≥0):=by
      exact_mod_cast hq.trans_le (show v≤v+t from le_add_of_nonneg_right (by positivity))
    have hq':(p.1:ℝ)<(v:ℝ):=by exact_mod_cast hq
    have hlN:p.1<v+t:=by exact_mod_cast hl
    simp[DeterministicItoShift.extend,hp,before,Set.indicator_apply,Set.mem_setOf_eq,hq',hq,hl,hlN,←NNReal.coe_add]

variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Exact SAME-J shifted constant-row stochastic coordinates. -/
theorem value(i:ι)(t:ℝ≥0)(ht:t≤h):
    RawCylindricalCoordinates.value (filtration 𝓕 v) μ h e
      (DeterministicItoShift.integral 𝓕 μ H v h hvh J) i t=ᵐ[μ]
      (fun ω=>RawCylindricalCoordinates.value 𝓕 μ H e J i (v+t) ω-
        RawCylindricalCoordinates.value 𝓕 μ H e J i v ω):=by
  have hh:(DeterministicItoShift.integral 𝓕 μ H v h hvh J).integral
      (stop (filtration 𝓕 v) μ h t (RawCylindricalCoordinates.row (filtration 𝓕 v) μ h e i))=
      J.integral (stop 𝓕 μ H (v+t) (RawCylindricalCoordinates.row 𝓕 μ H e i))-
        J.integral (stop 𝓕 μ H v (RawCylindricalCoordinates.row 𝓕 μ H e i)):=by
    change J.integral (DeterministicItoShift.input 𝓕 μ H v h hvh _) = _
    rw[input 𝓕 μ H v h hvh e i t ht,map_sub]
  change (fun ω=>(DeterministicItoShift.integral 𝓕 μ H v h hvh J).integral _ ω)=ᵐ[μ] _
  rw[hh]
  exact Lp.coeFn_sub _ _

variable[Countable ι][DecidableEq ι](he:Orthonormal ℝ e)

include he in
/-- The actual all-H continuous future coordinate is the SAME shifted
original integral coordinate, with no independent restart version. -/
theorem continuous_ae(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)(hpos:0<H)
    (i:ι)(t:ℝ≥0)(ht:t≤h):
    (fun ω=>RawCylindricalCoordinates.continuous 𝓕 μ H e J i (v+t) ω-
      RawCylindricalCoordinates.continuous 𝓕 μ H e J i v ω)=ᵐ[μ]
      RawCylindricalCoordinates.value (filtration 𝓕 v) μ h e
        (DeterministicItoShift.integral 𝓕 μ H v h hvh J) i t:=by
  exact ((AllHorizonCylindricalCoordinates.continuous_ae 𝓕 μ H e he J B hBDG hpos i (v+t)).sub
    (AllHorizonCylindricalCoordinates.continuous_ae 𝓕 μ H e he J B hBDG hpos i v)).trans
      (value 𝓕 μ H v h hvh e J i t ht).symm
end SHE.DeterministicItoShiftCoordinates
