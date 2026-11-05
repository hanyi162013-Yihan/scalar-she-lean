module
public import SHE.RawCylindricalCoordinates
public import SHE.GirsanovTransportWitness
public import SHE.StandardTerminalGirsanov
public import SHE.TimeMeasureRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.GirsanovRawCoordinates
open MeasureTheory ProbabilityTheory PredictableL2 StoppedItoInputs Set RawCylindricalCoordinates
open scoped NNReal ENNReal
variable {Ω C ι:Type}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[Countable ι][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)

theorem stopped_drift(t:ℝ≥0)(R u:Process (E:=C) 𝓕 μ H):
    (fun ω=>∫s,inner ℝ (stop 𝓕 μ H t R (s,ω)) (u (s,ω)) ∂timeMeasure H)=ᵐ[μ]
      (fun ω=>∫s,inner ℝ (R (s,ω)) (u (s,ω)) ∂timeMeasure (min t H)):=by
  have hs:=Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae (stop_ae 𝓕 μ H t R))
  filter_upwards [hs] with ω hω
  calc
    _=∫s,(Ioc 0 (min t H)).indicator (fun s=>inner ℝ (R (s,ω)) (u (s,ω))) s ∂timeMeasure H:=by
      apply integral_congr_ae
      filter_upwards [hω,timeMeasure_ae_mem H,(timeMeasure H).ae_ne t] with s hs hmem hne
      dsimp only [Prod.swap] at hs
      rw [hs]
      by_cases hst:s<t
      · have hs':(s,ω)∈before (Ω:=Ω) t:=by exact_mod_cast hst
        have hm:s∈Ioc 0 (min t H):=⟨hmem.1,le_min hst.le hmem.2⟩
        rw [Set.indicator_of_mem hs',Set.indicator_of_mem hm]
      · have hs':(s,ω)∉before (Ω:=Ω) t:=by exact_mod_cast hst
        have hm:s∉Ioc 0 (min t H):=fun h=>hst (lt_of_le_of_ne (h.2.trans (min_le_left _ _)) hne)
        rw [Set.indicator_of_notMem hs',Set.indicator_of_notMem hm,inner_zero_left]
    _=∫s,inner ℝ (R (s,ω)) (u (s,ω)) ∂timeMeasure (min t H):=by
      rw [integral_indicator measurableSet_Ioc,timeMeasure_restrict (min_le_right _ _)]

variable(e:ι→C)(he:Orthonormal ℝ e)
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable(Q:Measure Ω)[IsProbabilityMeasure Q]
variable(K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H)
variable(T:GirsanovTransportWitness 𝓕 μ Q H J K)
local notation "u"=>T.control
variable(hμQ:μ≪Q)(hQμ:Q≪μ)
variable(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)(hH:(H:ℝ)≤1)(hpos:0<H)
include he T hμQ hQμ hBDG hH hpos in
/-- The SAME chosen changed integral realizes the shifted original coordinate. -/
theorem coordinate_ae(i:ι)(t:ℝ≥0):
    RawCylindricalCoordinates.value 𝓕 Q H e K i t=ᵐ[Q]
      girsanovShift u (RawCylindricalCoordinates.row 𝓕 μ H e i)
        (RawCylindricalCoordinates.continuous 𝓕 μ H e J i) t:=by
  let R:=RawCylindricalCoordinates.row 𝓕 μ H e i
  let R':=RawCylindricalCoordinates.row 𝓕 Q H e i
  have hp:energyMeasure μ H≪energyMeasure Q H:=
    (Measure.AbsolutelyContinuous.refl (timeMeasure H)).prod hμQ
  have hmatch:∀ᵐ(p:ℝ≥0×Ω)∂energyMeasure μ H,stop 𝓕 μ H t R p=stop 𝓕 Q H t R' p:=by
    filter_upwards [stop_ae 𝓕 μ H t R,hp.ae_le (stop_ae 𝓕 Q H t R'),
      RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (e i),
      hp.ae_le (RotatedCylindricalCoordinates.constant_ae 𝓕 Q H (e i))] with p hs ht hR hR'
    rw [hs,ht]
    by_cases hin:p∈before (Ω:=Ω) t
    · rw [Set.indicator_of_mem hin,Set.indicator_of_mem hin]
      exact hR.trans hR'.symm
    · rw [Set.indicator_of_notMem hin,Set.indicator_of_notMem hin]
  filter_upwards [T.transport (stop 𝓕 μ H t R) (stop 𝓕 Q H t R') hmatch,
    hQμ.ae_le (RawCylindricalCoordinates.continuous_ae 𝓕 μ H e he J B hBDG hH hpos i t),
    hQμ.ae_le (stopped_drift 𝓕 μ H t R u)] with ω ht hc hd
  change K.integral (stop 𝓕 Q H t R') ω=_
  rw [ht,hd]
  change _=RawCylindricalCoordinates.continuous 𝓕 μ H e J i t ω+_
  rw [hc]
  rfl

include he T hμQ hQμ hBDG hH hpos in
/-- Recognition of the SAME changed raw driver using ordinary package7. -/
theorem law(hG:StandardTerminalGirsanov J)
    (hcap:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1)
    (hQ:Q=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
      (StochasticExponential.bracket 𝓕 μ H u))
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ):
    CylindricalDriverLaw.Law Q H (RawCylindricalCoordinates.value 𝓕 Q H e K):=by
  intro n a t ht
  have hLaw:=hG.finiteLaw u hcap n
    (fun i=>RawCylindricalCoordinates.row 𝓕 μ H e (a i))
    (fun i=>RawCylindricalCoordinates.continuous 𝓕 μ H e J (a i))
    (fun i j=>if a i=a j then 1 else 0) ?_ ?_ ?_ ?_
  · rw [←hQ] at hLaw
    apply (hLaw.1 t ht).congr
    filter_upwards [ae_all_iff.mpr (fun i:Fin n=>coordinate_ae 𝓕 μ H e he J Q K T hμQ hQμ B hBDG hH hpos (a i) (t i))] with ω hω
    apply PiLp.ext
    intro i
    exact hω i
  · intro i
    exact BoundedStoppedVersion.predictable_version 𝓕 μ H J (RawCylindricalCoordinates.row 𝓕 μ H e (a i)) hH hpos hnull B hBDG
      (by norm_num:0≤(1:ℝ)) (RawCylindricalCoordinates.row_norm 𝓕 μ H e he (a i))
  · intro i ω
    exact BoundedStoppedVersion.continuous_version 𝓕 μ H J (RawCylindricalCoordinates.row 𝓕 μ H e (a i)) hpos ω
  · intro s hs
    filter_upwards [ae_all_iff.mpr (fun i:Fin n=>RawCylindricalCoordinates.continuous_ae 𝓕 μ H e he J B hBDG hH hpos (a i) s)] with ω hω i
    exact hω i
  · filter_upwards [ae_all_iff.mpr (fun i:Fin n=>RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (e (a i)))] with p hp i j
    change inner ℝ (RotatedCylindricalCoordinates.constant 𝓕 μ H (e (a i)) p)
      (RotatedCylindricalCoordinates.constant 𝓕 μ H (e (a j)) p)=_
    rw [hp i,hp j]
    exact orthonormal_iff_ite.mp he (a i) (a j)
end SHE.GirsanovRawCoordinates
