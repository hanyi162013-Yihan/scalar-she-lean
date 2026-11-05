module

public import SHE.ForestJointTranslation
public import SHE.HistorySpatialSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HistoryProductMeasure
open Set Filter MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
  OrderedHeatForests
local instance historyRelativeSections_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩

def relativeSeparated (k : ℕ) :
    (Fin k→ℝ)×(HeatCircle×(Fin k→HeatCircle))→History HeatCircle k :=
  fun p=>separated k (p.2.1,p.1,fun i=>p.2.2 i+p.2.1)

/-- Original history measure, with old times first and all old spatial
locations translated by the actual output root. This triangular change
preserves the full product measure, including every restricted old time. -/
theorem relativeSeparated_preserving (R : ReferenceData) (k : ℕ) :
    MeasurePreserving (relativeSeparated k)
      ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
        (haarAddCircle.prod (Measure.pi (fun _ : Fin k=>haarAddCircle))))
      (historyMeasure R haarAddCircle k) := by
  let νt := Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let νx := (haarAddCircle : Measure HeatCircle)
  let νw := Measure.pi (fun _ : Fin k=>νx)
  have hshift := (MeasurePreserving.id νt).prod (jointRelativeShift_preserving k)
  have hswap := (measurePreserving_prodAssoc νx νt νw).comp
    (((Measure.measurePreserving_swap (μ:=νt) (ν:=νx)).prod (MeasurePreserving.id νw)).comp
      (measurePreserving_prodAssoc νt νx νw).symm)
  have h := (separated_measurePreserving R νx k).comp (hswap.comp hshift)
  convert! h using 1

/-- Almost-everywhere physical-history assertions remain valid on a
common old-time/root/relative-space event, even if their conclusion is
uniform over all current times. No measurability of an uncountable
intersection and no adaptive exceptional-set substitution is needed. -/
theorem ae_relative_spatial_sections (R : ReferenceData) (k : ℕ)
    {P : History HeatCircle k→Prop} (hP : ∀ᵐ p ∂historyMeasure R haarAddCircle k,P p) :
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐ x : HeatCircle ∂haarAddCircle,
      ∀ᵐ w : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
        P (separated k (x,t,fun i=>w i+x)) := by
  have h := (relativeSeparated_preserving R k).quasiMeasurePreserving.ae hP
  filter_upwards [Measure.ae_ae_of_ae_prod h] with t ht
  exact Measure.ae_ae_of_ae_prod ht

end SHE.HistoryProductMeasure
