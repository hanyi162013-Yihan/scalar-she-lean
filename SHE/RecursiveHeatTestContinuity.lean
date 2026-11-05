module

public import SHE.RecursiveHeatTargets
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.RecursiveHeatTestContinuity
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets SmoothWords SmoothCylinders UniformSmooth
open scoped NNReal
variable {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)

/-- The actual recursive Gaussian/insertion test is jointly continuous
in ε≥0 and its finite-dimensional argument, at every fixed history.
The covariance may become singular and an inserted heat age may vanish. -/
theorem continuous_test (k : ℕ) (p : History P k) :
    Continuous (fun q : ℝ≥0 × WordRecursion.State (n+k) => (level L δ hδ q.1 k).test p q.2) := by
  induction k with
  | zero => exact (L.test_uniform.smooth p).continuous.comp continuous_snd
  | succ k ih =>
    let F : ℝ≥0 → WordRecursion.State (n+k) → ℝ :=
      fun ε => (level L δ hδ ε k).test p.1
    have hF := ih p.1
    have hFs := uniform_reindex (test_uniform L δ hδ k) (fun ε : ℝ≥0 => (ε,p.1))
    let A := fun ε : ℝ≥0 => (level L δ hδ ε k).nodeCovariance p
    have hA := nodeCovariance_continuous L δ hδ k p
    have hH := GaussianParameterContinuity.continuous_average_hessian F hF hFs A hA
    have hp : Continuous (fun q : ℝ≥0 × WordRecursion.State (n+(k+1)) =>
        (q.1,SmoothWords.tailProjection (n+k) q.2)) :=
      continuous_fst.prodMk ((SmoothWords.tailProjection (n+k)).continuous.comp continuous_snd)
    have hH' := hH.comp hp
    have hr := (cutoffRow_continuous L δ hδ k p).comp
      (continuous_fst : Continuous (fun q : ℝ≥0 × WordRecursion.State (n+(k+1)) => q.1))
    have hd := (hH'.clm_apply hr).clm_apply hr
    have hc := R.totalVariance_smooth.smooth.continuous.comp
      ((SmoothWords.headProjection (n+k)).continuous.comp
        (continuous_snd : Continuous (fun q : ℝ≥0 × WordRecursion.State (n+(k+1)) => q.2)))
    have he : (fun ε : ℝ≥0 => R.reference ((level L δ hδ ε k).nodeTime p,p.2.2))=
        fun _ => R.reference ((level L δ hδ 0 k).nodeTime p,p.2.2) := by
      funext ε
      rw [nodeTime_eq L δ hδ ε 0 k p]
    have href : Continuous (fun q : ℝ≥0 × WordRecursion.State (n+(k+1)) =>
        R.reference ((level L δ hδ q.1 k).nodeTime p,p.2.2)) := by
      change Continuous ((fun ε : ℝ≥0 => R.reference ((level L δ hδ ε k).nodeTime p,p.2.2)) ∘ Prod.fst)
      rw [he]
      exact continuous_const
    exact ((continuous_const.mul (hc.sub href)).mul hd)

end SHE.RecursiveHeatTestContinuity
