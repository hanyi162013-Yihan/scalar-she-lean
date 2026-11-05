module

public import SHE.UniformInsertions
public import SHE.VariableObservations
public import SHE.MeasurableDerivatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual joint Borel induction for finite physical words. Singular
Gaussian covariances and merely measurable history parameters are allowed. -/
noncomputable section
namespace SHE.MeasurableWords
open Set MeasureTheory ProbabilityTheory StoppedFourier Matrix
open WordRecursion GaussianConvolution GaussianContinuity GaussianItoTest SmoothWords SmoothCylinders
open UniformSmooth UniformInsertions MeasurableDerivatives
open scoped MatrixOrder Matrix.Norms.L2Operator

abbrev State (n : ℕ) := WordRecursion.State n
variable {P : Type*} [MeasurableSpace P]

theorem gaussian_average_measurable {n : ℕ} {C : P → PositiveCovariance n} (hC : Measurable C)
    {F : P → State n → ℝ} (hF : Measurable (fun p : P × State n => F p.1 p.2))
    (hFc : ∀ p, Continuous (F p)) :
    Measurable (fun p : P × State n => gaussianAverage (C p.1).val (F p.1) p.2) := by
  have hs := (continuous_positive_sqrt n).measurable.comp hC
  have hact : Measurable (fun p : P × State n => toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C p.1).val) p.2) := by
    have heq : (fun p : P × State n => toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C p.1).val) p.2) =
        fun p => WithLp.toLp 2 (fun i => ∑ j, (CFC.sqrt (C p.1).val) i j * p.2 j) := by
      funext p
      apply (WithLp.equiv 2 (Fin n → ℝ)).injective
      exact Matrix.ofLp_toEuclideanCLM _ _
    rw [heq]
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    apply Finset.measurable_sum
    intro j _
    have hij : Measurable (fun p : P × State n => (CFC.sqrt (C p.1).val) i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hs.comp measurable_fst))
    have hcoord : Measurable (fun p : P × State n => p.2 j) :=
      (measurable_pi_apply j).comp ((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp measurable_snd)
    exact hij.mul hcoord
  let T : P × State n → State n := fun p => toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C p.1).val) p.2
  have hT : Measurable T := hact
  have hmap : Measurable (fun p : (P × State n) × State n => (p.1.1, p.1.2 + T (p.1.1, p.2))) := by
    have hp : Measurable (fun p : (P × State n) × State n => (p.1.1, p.2)) :=
      measurable_fst.fst.prodMk measurable_snd
    have hT' := hT.comp hp
    exact measurable_fst.fst.prodMk (measurable_fst.snd.add hT')
  have hi := (hF.comp hmap).stronglyMeasurable.integral_prod_right' (ν := stdGaussian (State n))
  have heq : (fun p : P × State n => gaussianAverage (C p.1).val (F p.1) p.2) =
      fun p => ∫ y : State n, F p.1 (p.2 + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C p.1).val) y)
        ∂stdGaussian (State n) := by
    funext p
    exact gaussian_integral_as_standard (F p.1) (hFc p.1) _ _
  rw [heq]
  exact hi.measurable

theorem insertion_measurable {n : ℕ} {a : ℝ → ℝ} (ha : Measurable a)
    (c : P → ℝ × HeatCircle → ℝ) (Z : P → Fin n → Observation) (t : P → ℝ) (x : P → HeatCircle)
    (hc : Measurable (fun p => c p (t p, x p)))
    (hrow : Measurable (fun p => heatRow (Z p) (t p) (x p)))
    {G : P → State n → ℝ} (hG : Measurable (fun p : P × State n => G p.1 p.2))
    (hGs : ∀ p, ContDiff ℝ 2 (G p)) :
    Measurable (fun p : P × State (n + 1) => insertion a (c p.1) (Z p.1) (t p.1) (x p.1) (G p.1) p.2) := by
  have hH := (hessian_measurable hG hGs).comp
    ((measurable_fst : Measurable (fun p : P × State (n + 1) => p.1)).prodMk
      ((tailProjection n).measurable.comp measurable_snd))
  have hq : Measurable (fun p : P × State (n + 1) => heatRow (Z p.1) (t p.1) (x p.1)) := hrow.comp measurable_fst
  have heval₁ : Continuous (fun p : (State n →L[ℝ] State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have heval₂ : Continuous (fun p : (State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hd := heval₂.measurable.comp ((heval₁.measurable.comp (hH.prodMk hq)).prodMk hq)
  have hcoef := (ha.comp ((headProjection n).measurable.comp measurable_snd)).sub (hc.comp measurable_fst)
  exact (hcoef.const_mul (1 / 2 : ℝ)).mul hd

def _root_.SHE.UniformInsertions.WordFamily.MeasurableData {n m : ℕ} {Z : P → Fin n → Observation} (word : WordFamily P Z m) : Prop :=
  match word with
  | .nil _ => True
  | .cons W _ t x _ _ _ _ _ _ _ _ rest =>
      Measurable (fun p => (W p).path (t p)) ∧
      Measurable (fun p => (W p).coefficient (t p, x p)) ∧
      Measurable (fun p => heatRow (Z p) (t p) (x p)) ∧ rest.MeasurableData

/-- The node hypotheses are Borel facts about the actual covariance,
physical row and reference value. VariableObservations derives them
from genuine target/center/profile families. No word measurability is
assumed in the induction. -/
theorem _root_.SHE.UniformInsertions.WordFamily.measurable {n m : ℕ} {Z : P → Fin n → Observation}
    (word : WordFamily P Z m) (hdata : word.MeasurableData)
    {a : ℝ → ℝ} (ha : BoundedSmooth a) {F : P → State n → ℝ}
    (hF : UniformBoundedSmooth F) (hFm : Measurable (fun p : P × State n => F p.1 p.2)) :
    Measurable (fun p : P × State m => word.apply a F p.1 p.2) := by
  induction word with
  | nil Z => exact hFm
  | cons W hZ t x ht hstop δ M hδ hM hgap hupper rest ih =>
    rcases hdata with ⟨hC, hc, hrow, hrest⟩
    have hG := hF.average (fun p => multivariateGaussian (0 : State _) ((W p).path (t p)).val)
      (fun _ => inferInstance)
    have hGm := gaussian_average_measurable hC hFm (fun p => (hF.smooth p).continuous)
    have hIm := insertion_measurable ha.smooth.continuous.measurable (fun p => (W p).coefficient) _ t x hc hrow hGm
      (fun p => (hG.smooth p).of_le (by simp))
    have hI := insertion_average_uniform ha hF (fun p => ((W p).path (t p)).val)
      (fun p => (W p).coefficient) _ t x hM
      (fun p => ((W p).bounded (t p) (Ioo_subset_Icc_self (ht p)) (x p)).trans (hupper p)) hδ hgap
    exact ih hrest hI hIm

end SHE.MeasurableWords
