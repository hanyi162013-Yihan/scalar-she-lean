module

public import SHE.ShiftedWordGeometry
public import SHE.PhysicalChainArrays
public import SHE.CoveredControlledLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.ShiftedPhysicalArrays
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry CoveredControlledLaw PhysicalScoreChain PhysicalChainArrays CoveredHistoryGeometry
variable {X : Type} [MeasurableSpace X] {R Q : ReferenceData} {n : ℕ}
variable (L : Level R X n) (K : Level Q X n) (v : ℝ)
variable (hb : Q.base=R.base+v) (hT : ∀ x,K.terminal x=L.terminal x+v)
variable (hZ : ∀ x,K.observations.observations x=ObservationTimeShift.observations v (L.observations.observations x))

theorem rootParameter_shift (k : ℕ) (p : History X k) :
    rootParameter k (shift v k p)=rootParameter k p := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact ih p.1

include hT in
theorem initialTerminal_shift (k : ℕ) (p : History X k) :
    initialTerminal K k (shift v k p)=initialTerminal L k p+v := by
  unfold initialTerminal
  rw [rootParameter_shift v k p]
  exact hT _

include hb hT hZ
theorem stops_shift (k : ℕ) (p : History X k) :
    stops K k (shift v k p)=fun i=>stops L k p i+v := by
  funext i
  unfold stops
  rw [observations_shift L K v hb hT hZ k p,initialTerminal_shift L K v hT k p]
  simp only [ObservationTimeShift.observations_stop,min_add_add_right]

theorem targets_shift (k : ℕ) (p : History X k) :
    targets K k (shift v k p)=fun i=>targets L k p i+v := by
  funext i
  unfold targets
  rw [observations_shift L K v hb hT hZ k p]
  rfl

theorem centers_shift (k : ℕ) (p : History X k) :
    centers K k (shift v k p)=centers L k p := by
  funext i
  unfold centers
  rw [observations_shift L K v hb hT hZ k p]
  rfl

end SHE.ShiftedPhysicalArrays
