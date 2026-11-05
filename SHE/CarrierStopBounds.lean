module

public import SHE.PhysicalParentGeometry
public import SHE.CoveredHistoryGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.CarrierStopBounds
open MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain
variable {X : Type} [MeasurableSpace X] {n : ℕ} {R : ReferenceData} (L : Level R X n)

/-- If the original stops end at the root terminal time, every inserted
stop also ends before that same original horizon. -/
theorem stop_le_initial (hσ : ∀ x i,(L.observations.observations x i).stop≤L.terminal x)
    (k : ℕ) (p : History X k) (i : Fin (n+k)) :
    ((carrier L k).observations.observations p i).stop≤ initialTerminal L k p := by
  induction k with
  | zero => exact hσ p i
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>ih p.1 j) i
    exact ((carrier L k).nodeTime_mem p).2.trans (terminal_le_initial L k p.1)

theorem clipped_observations_eq (hσ : ∀ x i,(L.observations.observations x i).stop≤L.terminal x)
    (k : ℕ) (p : History X k) :
    StoppedWindowCovariance.clipped ((carrier L k).observations.observations p) (initialTerminal L k p)=
      (carrier L k).observations.observations p := by
  funext i
  change (⟨min ((carrier L k).observations.observations p i).stop (initialTerminal L k p),
    ((carrier L k).observations.observations p i).target,
    ((carrier L k).observations.observations p i).center⟩ : Observation)=_
  rw [min_eq_left (stop_le_initial L hσ k p i)]

end SHE.CarrierStopBounds
