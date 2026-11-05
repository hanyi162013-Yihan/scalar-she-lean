module

public import SHE.MeasurableWords

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Zero extension of a physical insertion outside a time-separation
cutoff, while retaining the actual operator on the cutoff domain. -/
noncomputable section
namespace SHE.CutoffInsertionCore
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion GaussianItoTest SmoothWords SmoothCylinders UniformSmooth UniformInsertions MeasurableDerivatives

abbrev State (n : ℕ) := WordRecursion.State n
variable {P : Type*}

def core {n : ℕ} (a : ℝ → ℝ) (reference : ℝ) (row : State n)
    (G : State n → ℝ) (z : State (n + 1)) : ℝ :=
  (1 / 2 : ℝ) * (a (z 0) - reference) * directionalSecond G (tailProjection n z) row

theorem core_zero {n : ℕ} (a : ℝ → ℝ) (reference : ℝ) (G : State n → ℝ) :
    core a reference 0 G = 0 := by
  funext z
  simp only [core, directionalSecond, map_zero, mul_zero, Pi.zero_apply]

theorem core_uniform {n : ℕ} {a : ℝ → ℝ} (ha : BoundedSmooth a)
    {G : P → State n → ℝ} (hG : UniformBoundedSmooth G)
    (reference : P → ℝ) (row : P → State n) {M Q : ℝ}
    (hM : 0 ≤ M) (hreference : ∀ p, |reference p| ≤ M) (hQ : 0 ≤ Q) (hrow : ∀ p, ‖row p‖ ≤ Q) :
    UniformBoundedSmooth (fun p => core a (reference p) (row p) (G p)) := by
  have hdir := ((hG.fderiv.fderiv.apply_vector row hQ hrow).apply_vector row hQ hrow).comp_right (tailProjection n)
  have hcoef := ((UniformBoundedSmooth.fixed (P := P) ha).comp_right (headProjection n)).sub
    (UniformBoundedSmooth.parameter_const reference hM (fun p => by simpa only [Real.norm_eq_abs] using hreference p))
  have hhalf := UniformBoundedSmooth.parameter_const (P := P) (E := State (n + 1))
    (fun _ => (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun _ => by norm_num)
  exact (hhalf.mul hcoef).mul hdir

theorem core_measurable [MeasurableSpace P] {n : ℕ} {a : ℝ → ℝ} (ha : Measurable a)
    {reference : P → ℝ} (href : Measurable reference) {row : P → State n} (hrow : Measurable row)
    {G : P → State n → ℝ} (hG : Measurable (fun p : P × State n => G p.1 p.2))
    (hGs : ∀ p, ContDiff ℝ 2 (G p)) :
    Measurable (fun p : P × State (n + 1) => core a (reference p.1) (row p.1) (G p.1) p.2) := by
  have hH := (hessian_measurable hG hGs).comp
    ((measurable_fst : Measurable (fun p : P × State (n + 1) => p.1)).prodMk
      ((tailProjection n).measurable.comp measurable_snd))
  have hq : Measurable (fun p : P × State (n + 1) => row p.1) := hrow.comp measurable_fst
  have heval₁ : Continuous (fun p : (State n →L[ℝ] State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have heval₂ : Continuous (fun p : (State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hd := heval₂.measurable.comp ((heval₁.measurable.comp (hH.prodMk hq)).prodMk hq)
  have hc := (ha.comp ((headProjection n).measurable.comp measurable_snd)).sub (href.comp measurable_fst)
  exact (hc.const_mul (1 / 2 : ℝ)).mul hd

theorem core_cutoff_eq {n : ℕ} (a : ℝ → ℝ) (c : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (t : ℝ) (x : HeatCircle) (G : State n → ℝ) (good : Prop) [Decidable good] :
    core a (c (t, x)) (if good then heatRow Z t x else 0) G =
      if good then insertion a c Z t x G else 0 := by
  by_cases hg : good
  · simp only [hg, if_true]
    rfl
  · simp only [hg, if_false, core_zero]

end SHE.CutoffInsertionCore
