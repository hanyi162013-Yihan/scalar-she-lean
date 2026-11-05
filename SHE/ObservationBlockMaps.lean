module

public import SHE.GaussianAffineItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.ObservationBlockMaps
open GaussianIncrement
variable {k n : ℕ}

def restrict (e : Fin n→Fin k) : State k→L[ℝ]State n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : Fin k => ℝ) (e i)))

@[simp] theorem restrict_apply (e : Fin n→Fin k) (z : State k) (i : Fin n) :
    restrict e z i=z (e i) := rfl

def first (n : ℕ) : State (n+n)→L[ℝ]State n := restrict (Fin.castAdd n)
def second (n : ℕ) : State (n+n)→L[ℝ]State n := restrict (Fin.natAdd n)

@[simp] theorem first_apply (z : State (n+n)) (i : Fin n) : first n z i=z (Fin.castAdd n i) := rfl
@[simp] theorem second_apply (z : State (n+n)) (i : Fin n) : second n z i=z (Fin.natAdd n i) := rfl

@[simp] theorem first_append (f g : Fin n→ℝ) :
    first n (WithLp.toLp 2 (Fin.append f g))=WithLp.toLp 2 f := by
  apply PiLp.ext
  intro i
  exact Fin.append_left f g i

@[simp] theorem second_append (f g : Fin n→ℝ) :
    second n (WithLp.toLp 2 (Fin.append f g))=WithLp.toLp 2 g := by
  apply PiLp.ext
  intro i
  exact Fin.append_right f g i

end SHE.ObservationBlockMaps
