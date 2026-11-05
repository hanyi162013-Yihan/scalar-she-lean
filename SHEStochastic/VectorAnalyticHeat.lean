module

public import SHEStochastic.VectorHeatObservation
public import SHEStochastic.VectorPointHeatTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.VectorAnalyticHeat
open SHE SHE.StoppedFourier MatrixInfiniteHaar
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual unit-circle vector semigroup in the paper's physical
clock; its Fourier generator has eigenvalues -k^2. -/
def heat (t : ℝ) : Physical (d := d) →L[ℝ] Physical (d := d) :=
  VectorHeat.heat (t/NativeHeatObservation.timeScale)

theorem contraction (t : ℝ) (u : Physical (d := d)) : ‖heat t u‖ ≤ ‖u‖ :=
  VectorHeat.contraction _ u

theorem zero : heat (d := d) 0=ContinuousLinearMap.id ℝ (Physical (d := d)) := by
  simp only [heat,zero_div,VectorHeat.zero]

theorem semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heat (d := d) (s+t)=(heat s).comp (heat t) := by
  unfold heat
  rw [add_div,VectorHeat.semigroup (div_nonneg hs NativeHeatObservation.timeScale_pos.le)
    (div_nonneg ht NativeHeatObservation.timeScale_pos.le)]

theorem observation {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t)
    (x : HeatCircle) (u : Physical (d := d)) :
    VectorHeatObservation.observation ε x (heat t u)=VectorHeatObservation.observation (ε+t) x u := by
  have he := VectorHeatObservation.propagate hε (div_nonneg ht NativeHeatObservation.timeScale_pos.le) x u
  rw [mul_div_cancel₀ t NativeHeatObservation.timeScale_pos.ne'] at he
  exact he

/-- The adjoint heat flow propagates the literal analytic point tests,
with no missing circle normalization constant. -/
theorem test {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (x : HeatCircle) (i : d) :
    (heat t).adjoint (VectorPointHeatTest.test ε x i)=VectorPointHeatTest.test (ε+t) x i := by
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,VectorPointHeatTest.pairing hε,
    observation hε ht,VectorPointHeatTest.pairing (by linarith : 0 < ε+t)]

end SHEStochastic.VectorAnalyticHeat
