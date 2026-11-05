module
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.RecursiveScoreSupport
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeCarrierGeometry
open WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays CoveredControlledLaw
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ}
variable (L:Level R X n)

/-- All recursively inserted observations remain native when the
original root observations are native. No Gaussian/current law is used. -/
theorem carrier_native
    (hroot:∀x i,(L.observations.observations x i).stop=(L.observations.observations x i).target)
    (k:ℕ):∀h i,((carrier L k).observations.observations h i).stop=
      ((carrier L k).observations.observations h i).target:=by
  induction k with
  | zero=>exact hroot
  | succ k ih=>
    intro h i
    refine Fin.cases ?_ (fun j=>ih h.1 j) i
    change (carrier L k).nodeTime h=(carrier L k).nodeTime h+0
    exact (add_zero _).symm

/-- The covered-law stop clipping changes no native coordinate when
the original root stops lie before its initial terminal. -/
theorem stops_eq_targets
    (hroot:∀x i,(L.observations.observations x i).stop=(L.observations.observations x i).target)
    (hbound:∀x i,(L.observations.observations x i).stop≤L.terminal x)
    (k:ℕ) (h:History X k):stops L k h=targets L k h:=by
  funext i
  unfold stops targets
  rw [min_eq_left (CarrierStopBounds.stop_le_initial L hbound k h i)]
  exact carrier_native L hroot k h i

end SHE.NativeCarrierGeometry
