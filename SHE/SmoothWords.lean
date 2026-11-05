module

public import SHE.SmoothCylinderAlgebra
public import SHE.PhysicalIto

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-! Finite induction for the actual smooth covariance-insertion words.
Every node retains its original observation list and the newly appended
physical observation. Bounds are derived from genuine derivatives. -/
noncomputable section
namespace SHE.SmoothWords
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion GaussianItoTest CovarianceEndpoint SmoothCylinders
open scoped ContDiff

abbrev State (n : ℕ) := WordRecursion.State n

def headProjection (n : ℕ) : State (n + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0

def tailProjection (n : ℕ) : State (n + 1) →L[ℝ] State n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => z i.succ)
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }

theorem directionalSecond_boundedSmooth {n : ℕ} {F : State n → ℝ}
    (hF : BoundedSmooth F) (q : State n) :
    BoundedSmooth (fun z => directionalSecond F z q) := by
  have h₁ := hF.fderiv.fderiv.comp_left (ContinuousLinearMap.apply ℝ (State n →L[ℝ] ℝ) q)
  exact h₁.comp_left (ContinuousLinearMap.apply ℝ ℝ q)

theorem insertion_boundedSmooth {n : ℕ} {a : ℝ → ℝ} (ha : BoundedSmooth a)
    {G : State n → ℝ} (hG : BoundedSmooth G) (c : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (t : ℝ) (x : HeatCircle) :
    BoundedSmooth (insertion a c Z t x G) := by
  have hcoef := (ha.comp_right (headProjection n)).sub (BoundedSmooth.const (c (t, x)))
  have hdir := (directionalSecond_boundedSmooth hG (heatRow Z t x)).comp_right (tailProjection n)
  have hhalf : BoundedSmooth (fun _ : State (n + 1) => (1 / 2 : ℝ)) := BoundedSmooth.const _
  exact (hhalf.mul hcoef).mul hdir

theorem backward_boundedSmooth {n : ℕ} (W : EndpointWindow n) {F : State n → ℝ}
    (hF : BoundedSmooth F) (t : ℝ) : BoundedSmooth (backward W F t) :=
  BoundedSmooth.average (multivariateGaussian 0 (W.path t).val) hF

/-- The terminal index is the actual final cylinder dimension. A node
lies before every original stop, and the next node contains the literal
new observation with stop and target equal to the insertion time. -/
inductive PhysicalWord : {n : ℕ} → (Fin n → Observation) → ℕ → Type
  | nil {n : ℕ} (Z : Fin n → Observation) : PhysicalWord Z n
  | cons {n m : ℕ} {Z : Fin n → Observation}
      (W : EndpointWindow n) (same_observations : W.observations = Z)
      (time : ℝ) (space : HeatCircle) (time_in : time ∈ Ioo W.left W.right)
      (before_stops : ∀ i, W.right ≤ (Z i).stop)
      (rest : PhysicalWord (appendObservation Z time space) m) : PhysicalWord Z m

def PhysicalWord.apply {n m : ℕ} {Z : Fin n → Observation}
    (word : PhysicalWord Z m) (a : ℝ → ℝ) (F : State n → ℝ) : State m → ℝ :=
  match word with
  | .nil _ => F
  | .cons W _ t x _ _ rest => rest.apply a (insertion a W.coefficient Z t x (backward W F t))

/-- Genuine finite induction on the printed Gaussian-average/insertion
operators. No derivative bound on an unexplained word is assumed. -/
theorem PhysicalWord.boundedSmooth {n m : ℕ} {Z : Fin n → Observation}
    (word : PhysicalWord Z m) {a : ℝ → ℝ} (ha : BoundedSmooth a)
    {F : State n → ℝ} (hF : BoundedSmooth F) : BoundedSmooth (word.apply a F) := by
  induction word with
  | nil Z => exact hF
  | cons W hZ t x ht hstop rest ih =>
    exact ih (insertion_boundedSmooth ha (backward_boundedSmooth W hF t) W.coefficient _ t x)

/-- Every actual smooth word supplies all deterministic hypotheses for
the next finite-dimensional Itô step, including terminal-time AC. -/
theorem boundedSmooth_backward_regular {n : ℕ} (W : EndpointWindow n)
    {F : State n → ℝ} (hF : BoundedSmooth F) :
    RegularTest W.left W.right (backward W F) (backwardDerivative W F) := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  obtain ⟨M, hM⟩ := hF.norm_bound
  obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
  obtain ⟨B, hB⟩ := hF.hessian_norm_bound
  obtain ⟨K, hKn, hK⟩ := hF.hessian_lipschitz
  exact backward_regular W (hF.smooth.of_le (by simp)) hM hL hB
    ((norm_nonneg (GaussianTaylor.hessian F 0)).trans (hB 0)) hKn hK

end SHE.SmoothWords
