module

public import SHEStochastic.FourierCylinderGenerator
public import SHEStochastic.FourierDiagonalFlow

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.FiniteStateDriverCoordinates
open SHE SHE.DyadicApproximation GaussianItoTest
open scoped NNReal

variable {s d : ℕ}

def append (z : State s) (w : State d) : State (s + d) := WithLp.toLp 2 (Fin.addCases z w)

@[simp] theorem append_left (z : State s) (w : State d) (i : Fin s) :
    append z w (Fin.castAdd d i) = z i := by simp [append]

@[simp] theorem append_right (z : State s) (w : State d) (j : Fin d) :
    append z w (Fin.natAdd s j) = w j := by simp [append]

theorem continuous_append : Continuous (fun p : State s × State d ↦ append p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (s + d) ↦ ℝ)).comp
  apply continuous_pi
  refine Fin.addCases ?_ ?_
  · intro i
    simp only [Fin.addCases_left]
    convert (PiLp.continuous_apply 2 (fun _ : Fin s ↦ ℝ) i).comp
      (continuous_fst : Continuous (Prod.fst : State s × State d → State s)) using 1 <;> rfl
  · intro j
    simp only [Fin.addCases_right]
    convert (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) j).comp
      (continuous_snd : Continuous (Prod.snd : State s × State d → State d)) using 1 <;> rfl

/-- State frequencies retain their heat decay; driver coordinates have
zero heat frequency and are unchanged by the integrating factor. -/
def frequencies (n : Fin s → ℤ) : Fin (s + d) → ℤ := Fin.addCases n (fun _ ↦ 0)

theorem raw_append (n : Fin s → ℤ) (t : ℝ) (z : State s) (w : State d) :
    FourierDiagonalFlow.raw (frequencies (d := d) n) t (append z w) =
      append (FourierDiagonalFlow.raw n t z) w := by
  apply PiLp.ext
  refine Fin.addCases ?_ ?_
  · intro i
    simp [FourierDiagonalFlow.raw_apply, frequencies, append]
  · intro j
    simp [FourierDiagonalFlow.raw_apply, frequencies, append]

theorem clamped_append (H : ℝ) (n : Fin s → ℤ) (t : ℝ) (z : State s) (w : State d) :
    FourierDiagonalFlow.clamped H (frequencies (d := d) n) t (append z w) =
      append (FourierDiagonalFlow.clamped H n t z) w :=
  raw_append n (ClampedAbsoluteContinuity.clamp 0 H t) z w

variable {ι : Type*} (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ) (driver : Fin d → ι)

def projection (q : RealL2 × (ι → ℝ)) : State (s + d) :=
  append (FourierCylinderGenerator.projection a n q.1) (WithLp.toLp 2 (fun j ↦ q.2 (driver j)))

theorem continuous_projection : Continuous (projection a n driver) :=
  continuous_append.comp (((FourierCylinderGenerator.projection a n).continuous.comp continuous_fst).prodMk
    ((PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
      (continuous_pi fun j ↦ (continuous_apply (driver j)).comp continuous_snd)))

def projectionMap : C(RealL2 × (ι → ℝ), State (s + d)) := ⟨projection a n driver, continuous_projection a n driver⟩

@[simp] theorem projection_left (q : RealL2 × (ι → ℝ)) (i : Fin s) :
    projection a n driver q (Fin.castAdd d i) = FourierCylinderGenerator.projection a n q.1 i := by
  simp [projection]

@[simp] theorem projection_right (q : RealL2 × (ι → ℝ)) (j : Fin d) :
    projection a n driver q (Fin.natAdd s j) = q.2 (driver j) := by
  simp [projection]

end SHEStochastic.FiniteStateDriverCoordinates
