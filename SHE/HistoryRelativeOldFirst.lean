module

public import SHE.HistoryRelativeSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HistoryProductMeasure
open Set Filter MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- The original common history event with old relative locations
before the output root. This preserves assertions uniform in arbitrary
current times and parameters, without measurability of an uncountable
intersection or substitution into a fixed-root exceptional set. -/
theorem ae_relative_old_first (R : ReferenceData) (k : ℕ)
    {P : History HeatCircle k→Prop} (hP : ∀ᵐ h ∂historyMeasure R haarAddCircle k,P h) :
    ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐ w : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      ∀ᵐ x : HeatCircle ∂haarAddCircle,
        P (separated k (x,t,fun i=>w i+x)) := by
  let νt := Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let νx : Measure HeatCircle := haarAddCircle
  let νw := Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  have hswap := (MeasurePreserving.id νt).prod (Measure.measurePreserving_swap (μ:=νw) (ν:=νx))
  have hmap := (relativeSeparated_preserving R k).comp hswap
  have he := hmap.quasiMeasurePreserving.ae hP
  filter_upwards [Measure.ae_ae_of_ae_prod he] with t ht
  exact Measure.ae_ae_of_ae_prod ht

end SHE.HistoryProductMeasure
