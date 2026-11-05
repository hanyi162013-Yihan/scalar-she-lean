module

public import SHE.HistoryRelativeSections
public import SHE.CircleNormalization

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

namespace SHE.DefectHistorySections
open Set MeasureTheory AddCircle StoppedFourier CutoffWordHistories HistoryProductMeasure WordRecursion CutoffWordLevel
local instance defectHistorySections_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance defectHistorySections_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- A genuine original-history event is selected BEFORE every
uncountable parameter. It remains one event with old time and relative
old space outside the output root integral. -/
theorem common_event (R:ReferenceData)(k:ℕ){P:History HeatCircle k→Prop}
    (hP:∀ᵐh∂historyMeasure R haarAddCircle k,P h):
    ∀ᵐt:Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐw:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
        ∀ᵐx:HeatCircle ∂haarAddCircle,P (separated k (x,t,fun i=>w i+x)):=by
  let τ:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let ν:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  have hp:=(relativeSeparated_preserving R k).quasiMeasurePreserving.ae hP
  have hs:=(MeasurePreserving.id τ).prod
    (Measure.measurePreserving_swap (μ:=ν) (ν:=(haarAddCircle:Measure HeatCircle)))
  have hh:=hs.quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hh] with t ht
  exact Measure.ae_ae_of_ae_prod ht

private theorem root_event {P:HeatCircle→Prop}
    (hP:∀ᵐx:HeatCircle∂haarAddCircle,P x):
    ∀ᵐx:AddCircle (1:ℝ)∂haarAddCircle,
      P (CircleNormalization.scale 1 (2*Real.pi) x):=by
  exact (CircleNormalization.scale_measurePreserving 1 (2*Real.pi)).quasiMeasurePreserving.ae hP

theorem unit_common_event (R:ReferenceData)(k:ℕ){P:History HeatCircle k→Prop}
    (hP:∀ᵐh∂historyMeasure R haarAddCircle k,P h):
    ∀ᵐt:Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐw:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
        ∀ᵐx:AddCircle (1:ℝ) ∂haarAddCircle,
          P (separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
            fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)):=by
  apply (common_event R k hP).mono
  intro t ht
  apply ht.mono
  intro w hw
  exact root_event (P:=fun x:HeatCircle=>P (separated k (x,t,fun i=>w i+x))) hw

end SHE.DefectHistorySections
