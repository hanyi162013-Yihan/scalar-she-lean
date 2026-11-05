module

public import SHE.CutoffCarriers

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CarrierNativeObservations
open WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

/-- Native root observations and native recursive insertions preserve
stop=target at every original coordinate of the carrier. -/
theorem carrier_native (L : CutoffWordLevel.Level R X n)
    (hn : ∀ x i,(L.observations.observations x i).stop=(L.observations.observations x i).target)
    (k : ℕ) (h : History X k) (i : Fin (n+k)) :
    ((carrier L k).observations.observations h i).stop=
      ((carrier L k).observations.observations h i).target := by
  induction k with
  | zero => exact hn h i
  | succ k ih =>
    refine Fin.cases ?_ (fun j=>ih h.1 j) i
    change (carrier L k).nodeTime h=(carrier L k).nodeTime h+0
    rw [add_zero]

end SHE.CarrierNativeObservations
