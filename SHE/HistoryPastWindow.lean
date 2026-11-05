module

public import SHE.CutoffCarriers
public import SHE.HistoryGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.HistoryPastWindow
open Set MeasureTheory CutoffWordLevel CutoffWordHistories CutoffCarriers StoppedFourier
local instance historyPastWindow_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X : Type*} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- Every original sampled node lies strictly after the original past.
This statement concerns the true node measure, not the good histories
weighted by a test or a cutoff. -/
theorem node_after_past : ∀ᵐ p ∂nodeMeasure R,R.base<p.1 := by
  have ht : ∀ᵐ t ∂volume.restrict (Ioc R.base R.horizon),R.base<t:=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ h=>h.1)
  exact Measure.quasiMeasurePreserving_fst.ae ht

/-- The current front at the original past is inside every sampled
finite carrier window on one common original-history event. -/
theorem carrier_after_past_ae (L : Level R X n) (hL : ∀ x,R.base<L.terminal x)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure R ρ k,R.base<(carrier L k).terminal h := by
  induction k with
  | zero =>exact ae_of_all _ hL
  | succ k ih =>
    have hhead : ∀ᵐ p ∂(historyMeasure R ρ k).prod (nodeMeasure R),R.base<(carrier L k).terminal p.1:=
      Measure.quasiMeasurePreserving_fst.ae ih
    have hnode : ∀ᵐ p ∂(historyMeasure R ρ k).prod (nodeMeasure R),R.base<p.2.1:=
      Measure.quasiMeasurePreserving_snd.ae (node_after_past (R:=R))
    filter_upwards [hhead,hnode] with p hp ht
    change R.base<max R.base (min ((carrier L k).terminal p.1) p.2.1)
    exact (lt_min hp ht).trans_le (le_max_right _ _)

end SHE.HistoryPastWindow
