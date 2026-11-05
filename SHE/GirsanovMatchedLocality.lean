module
public import SHE.GirsanovTransportWitness
public import SHE.StandardTerminalPastLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.GirsanovIntegralTransport
open MeasureTheory PredictableL2 PastItoInputs Set
open scoped NNReal ENNReal
variable {Ω C:Type}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)

/-- The compensator has the same deterministic-past event pullout.
This is literal time integration of the actual predictable inputs. -/
theorem event_drift(v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A)
    (f u:Process (E:=C) 𝓕 μ H):
    (fun ω=>∫s,inner ℝ (eventProcess 𝓕 μ H v A hA f (s,ω)) (u (s,ω)) ∂timeMeasure H)=ᵐ[μ]
      A.indicator (fun ω=>∫s,inner ℝ (post 𝓕 μ H v f (s,ω)) (u (s,ω)) ∂timeMeasure H):=by
  have he:=Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae (eventProcess_ae 𝓕 μ H v A hA f))
  have hp:=Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
    (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae (post_ae 𝓕 μ H v f))
  filter_upwards [he,hp] with ω he hp
  by_cases hω:ω∈A
  · rw [Set.indicator_of_mem hω]
    apply integral_congr_ae
    filter_upwards [he,hp] with s hs ht
    dsimp only [Prod.swap] at hs ht
    rw [hs,ht]
    by_cases hvs:v<s
    · rw [Set.indicator_of_mem (show (s,ω)∈eventAfter v A from ⟨hvs,hω⟩),if_pos hvs]
    · rw [Set.indicator_of_notMem (show (s,ω)∉eventAfter v A from fun h=>hvs h.1),if_neg hvs]
  · rw [Set.indicator_of_notMem hω]
    apply integral_eq_zero_of_ae
    filter_upwards [he] with s hs
    dsimp only [Prod.swap] at hs
    rw [hs,Set.indicator_of_notMem (show (s,ω)∉eventAfter v A from fun h=>hω h.2)]
    simp only [inner_zero_left,Pi.zero_apply]

variable(Q:Measure Ω)[IsProbabilityMeasure Q]
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable(K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H)
variable(T:GirsanovTransportWitness 𝓕 μ Q H J K)
local notation "u"=>T.control
local notation "hT"=>T.transport
variable(hμQ:μ≪Q)(hQμ:Q≪μ)(hlocal:StandardTerminalPastLocality J)
include T hμQ hQμ hlocal in
/-- Ordinary Girsanov transport preserves deterministic-past locality
on every actual input that belongs to both original L2 spaces. -/
theorem locality_matched(v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A)
    (f:Process (E:=C) 𝓕 μ H)(g:Process (E:=C) 𝓕 Q H)
    (hfg:∀ᵐ(p:ℝ≥0×Ω)∂energyMeasure μ H,f p=g p):
    K.integral (eventProcess 𝓕 Q H v A hA g)=ᵐ[Q]
      A.indicator (K.integral (post 𝓕 Q H v g)):=by
  have hprod:energyMeasure μ H≪energyMeasure Q H:=
    (Measure.AbsolutelyContinuous.refl (timeMeasure H)).prod hμQ
  have he:∀ᵐp∂energyMeasure μ H,eventProcess 𝓕 μ H v A hA f p=eventProcess 𝓕 Q H v A hA g p:=by
    filter_upwards [eventProcess_ae 𝓕 μ H v A hA f,
      hprod.ae_le (eventProcess_ae 𝓕 Q H v A hA g),hfg] with p hp hq hfg
    rw [hp,hq]
    by_cases hin:p∈eventAfter v A
    · rw [Set.indicator_of_mem hin,Set.indicator_of_mem hin,hfg]
    · rw [Set.indicator_of_notMem hin,Set.indicator_of_notMem hin]
  have hp:∀ᵐp∂energyMeasure μ H,post 𝓕 μ H v f p=post 𝓕 Q H v g p:=by
    filter_upwards [post_ae 𝓕 μ H v f,hprod.ae_le (post_ae 𝓕 Q H v g),hfg] with p hp hq hfg
    rw [hp,hq,hfg]
  filter_upwards [hT (eventProcess 𝓕 μ H v A hA f) (eventProcess 𝓕 Q H v A hA g) he,
    hT (post 𝓕 μ H v f) (post 𝓕 Q H v g) hp,
    hQμ.ae_le (hlocal v A hA f),hQμ.ae_le (event_drift 𝓕 μ H v A hA f u)] with ω he hp hl hd
  rw [he,hl,hd]
  by_cases hω:ω∈A
  · simp only [Set.indicator_of_mem hω]
    exact hp.symm
  · simp only [Set.indicator_of_notMem hω,zero_add]
end SHE.GirsanovIntegralTransport
