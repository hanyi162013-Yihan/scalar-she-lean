module

public import SHE.UniformSmooth
public import SHE.ObservationBlockMaps

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.FiniteComparisonTest
open SmoothCylinders UniformSmooth GaussianIncrement
variable (n : ℕ)

def left : State (n+n)→L[ℝ]State n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i=>PiLp.proj 2 (fun _ : Fin (n+n)=>ℝ) (Fin.castAdd n i)))

def right : State (n+n)→L[ℝ]State n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i=>PiLp.proj 2 (fun _ : Fin (n+n)=>ℝ) (Fin.natAdd n i)))

@[simp] theorem left_apply (z : State (n+n)) (i : Fin n) : left n z i=z (Fin.castAdd n i) := rfl
@[simp] theorem right_apply (z : State (n+n)) (i : Fin n) : right n z i=z (Fin.natAdd n i) := rfl

def test (F : State n→ℝ) (z : State (n+n)) : ℝ := F (left n z)-F (right n z)

/-- The internal two-copy test preserves genuine all-order bounded
smoothness of a scalar terminal test. -/
theorem boundedSmooth {F : State n→ℝ} (hF : BoundedSmooth F) : BoundedSmooth (test n F) := by
  have hU : UniformBoundedSmooth (fun _ : Unit=>F) := UniformBoundedSmooth.fixed hF
  have hl := hU.comp_right (left n)
  have hr := hU.comp_right (right n)
  have hd := hl.sub hr
  exact ⟨hd.smooth (),fun k=>by
    obtain ⟨C,hC⟩:=hd.bounds k
    exact ⟨C,hC.2 ()⟩⟩

end SHE.FiniteComparisonTest
