module

public import SHE.RootBackwardHessian
public import SHE.JointObservationTargetContinuity
public import SHE.JointWordHessian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.RootJointHessian
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RootHeatBounds RootHeatTargets JointWordAnalytic Filter Topology
open scoped NNReal
local instance rootJointHessian_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance rootJointHessian_sigma : MeasurableSpace CircleL2 := borel _
local instance rootJointHessian_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (δ : ℝ) (hδ : 0<δ) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

theorem continuous_state (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t<(level L δ hδ 0 k).terminal p) :
    Continuous (fun ε : ℝ≥0 => state (level L δ hδ ε k) Λ U V XU XV p ω t) := by
  have hσ (i : Fin (n+k)) : Continuous (fun ε : ℝ≥0 =>
      ((level L δ hδ ε k).observations.observations p i).stop) := by
    convert (continuous_const (y := ((level L δ hδ 0 k).observations.observations p i).stop)) using 1
    funext ε
    exact stop_eq L δ hδ ε 0 k p i
  have hgap (ε : ℝ≥0) (i : Fin (n+k)) : t<((level L δ hδ ε k).observations.observations p i).target := by
    have hh := (level L δ hδ ε k).targets_after p i
    rw [terminal_eq L δ hδ ε 0 k p] at hh
    exact ht.trans_le hh
  exact JointObservationTargetContinuity.continuous_evaluate Λ
    (fun ε => (level L δ hδ ε k).observations.observations p)
    (fun i => ((level L δ hδ 0 k).observations.observations p i).center)
    (target_continuous L δ hδ k p) hσ (fun ε i => center_eq L δ hδ ε 0 k p i)
    t hgap (fun s => U (ω,s)) (fun s => V (ω,s)) (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx))

theorem continuous_field (k : ℕ) (p : History P k) (ω : Ω) {t : ℝ}
    (ht : t<(level L δ hδ 0 k).terminal p) :
    Continuous (fun ε : ℝ≥0 => JointWordHessian.field (level L δ hδ ε k) Λ U V XU XV ((p,ω),t)) := by
  have hc := (RootBackwardHessian.continuous_backward_hessian L δ hδ k p t).comp
    (continuous_id.prodMk (continuous_state L δ hδ Λ U V XU XV k p ω ht))
  convert hc using 1
  funext ε
  rfl

/-- Uniformity in epsilon is derived from the actual recursively built
smooth tests. The finite depth and fixed positive delta remain explicit. -/
theorem field_uniform_bound (k : ℕ) : ∃ B : ℝ,0≤B ∧ ∀ ε : ℝ≥0,∀ p ω t,
    ‖JointWordHessian.field (level L δ hδ ε k) Λ U V XU XV ((p,ω),t)‖≤B := by
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩ := (test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  refine ⟨B,hBn,fun ε p ω t => ?_⟩
  exact BackwardRegularity.gaussian_state_hessian_bound _
    (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp))
    (hC (ε,p)) (hD (ε,p)) (hB (ε,p)) _

end SHE.RootJointHessian
