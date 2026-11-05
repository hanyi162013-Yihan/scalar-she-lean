module

public import SHE.RootFiniteSums
public import SHE.CoveredControlledLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootFiniteGeometry
open MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  SmoothCylinders UniformSmooth CoveredControlledLaw
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n) (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
  (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "K"=>RootFiniteSums.withRoot L F hF hFm

theorem terminal_eq (k : ℕ) (p : History X k) : (carrier K k).terminal p=(carrier L k).terminal p :=
  CarrierGeometryCongruence.terminal K L rfl (fun _=>rfl) k p

theorem observations_eq (k : ℕ) (p : History X k) :
    (carrier K k).observations.observations p=(carrier L k).observations.observations p :=
  CarrierGeometryCongruence.observations K L rfl (fun _=>rfl) (fun _=>rfl) k p

theorem stops_eq (k : ℕ) (p : History X k) : stops K k p=stops L k p := by
  unfold stops
  rw [observations_eq L F hF hFm k p]
  rfl

theorem targets_eq (k : ℕ) (p : History X k) : targets K k p=targets L k p := by
  unfold targets
  rw [observations_eq L F hF hFm k p]

theorem centers_eq (k : ℕ) (p : History X k) : centers K k p=centers L k p := by
  unfold centers
  rw [observations_eq L F hF hFm k p]
end SHE.RootFiniteGeometry
