module

public import SHE.PhysicalInsertion
public import SHE.NativeControlledGenerator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.JointPhysicalInsertion
open MeasureTheory Set WordRecursion GaussianItoTest GaussianTaylor GaussianTaylorAverage
open PhysicalInsertion CovarianceEndpoint StoppedFourier
local instance jointPhysicalInsertion_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
abbrev State (n : ℕ) := WordRecursion.State n

def appendState {n : ℕ} (x : ℝ) (z : State n) : State (n+1) := WithLp.toLp 2 (Fin.cons x z.ofLp)

@[simp] theorem appendState_zero {n : ℕ} (x : ℝ) (z : State n) : appendState x z 0=x := rfl
@[simp] theorem appendState_succ {n : ℕ} (x : ℝ) (z : State n) (i : Fin n) : appendState x z i.succ=z i := rfl

theorem insertion_appendState {n : ℕ} (a : ℝ→ℝ) (c : ℝ×HeatCircle→ℝ)
    (Z : Fin n→Observation) (t : ℝ) (x : HeatCircle) (F : State n→ℝ) (v : ℝ) (z : State n) :
    insertion a c Z t x F (appendState v z)=
      (1/2:ℝ)*(a v-c (t,x))*GaussianTaylor.hessian F z (heatRow Z t x) (heatRow Z t x) := by
  rw [insertion,appendState_zero]
  have he : WithLp.toLp 2 (fun i : Fin n => appendState v z i.succ)=z := by
    apply PiLp.ext
    intro i
    rfl
  rw [he]
  rfl

/-- Local coefficient insertion at an arbitrary joint old state. The
newest coordinate is the actual V point; all old joint coordinates are
kept unchanged. A separately retained defect mark is not expanded. -/
theorem insertion_and_defect {n : ℕ} (W : EndpointWindow n)
    (a : ℝ→ℝ) (ha : Measurable a) (X : ℝ×HeatCircle→ℝ) (hX : Measurable X)
    {A : ℝ} (hA : 0≤A) (hbound : ∀ z,|a z|≤A) (F : State n→ℝ)
    {t : ℝ} (ht : t∈Ioo W.left W.right) (z : State n)
    (E : Matrix (Fin n) (Fin n) ℝ) :
    backwardDerivative W F t z+(1/2:ℝ)*covarianceAction
      (CovarianceMatrix.densityMatrix (fun p => a (X p)) W.observations t+E)
      (GaussianTaylor.hessian (backward W F t) z)=
      (∫ x : HeatCircle,insertion a W.coefficient W.observations t x (backward W F t)
        (appendState (X (t,x)) z) ∂AddCircle.haarAddCircle)+
      (1/2:ℝ)*covarianceAction E (GaussianTaylor.hessian (backward W F t) z) := by
  have hc := mixed_pair_cancellation W (fun p => a (X p)) (ha.comp hX) hA ht
    (fun x => hbound (X (t,x))) (GaussianTaylor.hessian (backward W F t) z)
  have he : covarianceAction
      (CovarianceMatrix.densityMatrix (fun p => a (X p)) W.observations t+E)
      (GaussianTaylor.hessian (backward W F t) z)=
      covarianceAction (CovarianceMatrix.densityMatrix (fun p => a (X p)) W.observations t)
        (GaussianTaylor.hessian (backward W F t) z)+covarianceAction E (GaussianTaylor.hessian (backward W F t) z) := by
    simp only [covarianceAction,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
  simp_rw [insertion_appendState]
  rw [he]
  change -(1/2:ℝ)*_+(1/2:ℝ)*(_+_) = _+_
  linarith

end SHE.JointPhysicalInsertion
