module

public import SHE.CoveredControlledLaw
public import SHE.UncutNewestState

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.TerminalSuccessorGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry PhysicalScoreChain
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ}

def atSpace {k:ℕ} (p:History X (k+1)) (x:HeatCircle):History X (k+1):=(p.1,(p.2.1,x))

theorem nodeTime_atSpace (L:Level R X n) (k:ℕ) (p:History X (k+1)) (x:HeatCircle):
    (carrier L k).nodeTime (atSpace p x)=(carrier L k).nodeTime p := rfl

theorem lower_atSpace (L:Level R X n) (k:ℕ) (p:History X (k+1)) (x:HeatCircle):
    lower L (k+1) (atSpace p x)=lower L (k+1) p := rfl

theorem upper_atSpace (L:Level R X n) (k:ℕ) (p:History X (k+1)) (x:HeatCircle):
    upper L (k+1) (atSpace p x)=upper L (k+1) p := rfl

/-- The actual newest coordinate has zero future age, while every old
stop/target remains its ORIGINAL covered value. -/
theorem stops_succ (L:Level R X n) (k:ℕ) (p:History X (k+1)):
    stops L (k+1) p=Fin.cons ((carrier L k).nodeTime p) (stops L k p.1) := by
  funext i
  refine Fin.cases ?_ (fun j=>rfl) i
  change min ((carrier L k).nodeTime p) (initialTerminal L k p.1)=_
  exact min_eq_left (((carrier L k).nodeTime_mem p).2.trans (terminal_le_initial L k p.1))

theorem targets_succ (L:Level R X n) (k:ℕ) (p:History X (k+1)):
    targets L (k+1) p=Fin.cons ((carrier L k).nodeTime p) (targets L k p.1) := by
  funext i
  refine Fin.cases ?_ (fun j=>rfl) i
  change (carrier L k).nodeTime p+0=(carrier L k).nodeTime p
  rw [add_zero]

theorem centers_succ (L:Level R X n) (k:ℕ) (p:History X (k+1)):
    centers L (k+1) p=Fin.cons p.2.2 (centers L k p.1) := by
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

/-- Changing only the newest spatial point leaves every old time gap
fixed. These are the exact sections used by endpoint conditional Fubini. -/
theorem relative_arrays_atSpace (L:Level R X n) (v:ℝ) (k:ℕ) (p:History X (k+1)) (x:HeatCircle):
    (fun i=>stops L (k+1) (atSpace p x) i-v)=
        Fin.cons ((carrier L k).nodeTime p-v) (fun i=>stops L k p.1 i-v) ∧
      (fun i=>targets L (k+1) (atSpace p x) i-v)=
        Fin.cons ((carrier L k).nodeTime p-v) (fun i=>targets L k p.1 i-v) ∧
      centers L (k+1) (atSpace p x)=Fin.cons x (centers L k p.1) := by
  refine ⟨?_,?_,?_⟩
  · rw [stops_succ]
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  · rw [targets_succ]
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  · exact centers_succ L k (atSpace p x)

end SHE.TerminalSuccessorGeometry
