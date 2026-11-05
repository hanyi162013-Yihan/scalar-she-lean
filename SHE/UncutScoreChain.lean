module

public import SHE.ProjectedUncutWord
public import SHE.FiniteScoreIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ProjectedUncutWord
open Set MeasureTheory ProbabilityTheory WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers SmoothCylinders GaussianCoordinates TriangularScoreWords
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- A finite chain of exact original-coordinate covariance restrictions.
The PSD and range fields are applicability obligations on the physical
covariances; no unproved comparison bound occurs in this data. -/
inductive Chain : (k : ℕ) → History P k → (Fin (n+k) → Fin N) → Type
  | root (p : P) (f : Fin n → Fin N) : Chain 0 p f
  | step (k : ℕ) (p : History P (k+1))
      (f : Fin (n+k) → Fin N) (g : Fin (n+k+1) → Fin N)
      (prev : Chain k p.1 f) (htail : ∀ i, g i.succ = f i)
      (old residual : MeasurableGeneralizedInverse.Mat N)
      (ho : old.PosSemidef) (hr : residual.PosSemidef)
      (hcov : (old + residual).submatrix f f = ((carrier L k).nodeCovariance p).val)
      (d : WordRecursion.State N) (hd : projection f d = row L k p)
      (hrange : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) old).range) : Chain (k+1) p g

def Chain.word {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Word (WordRecursion.State N × WordRecursion.State N) N :=
  match chain with
  | .root _ _ => []
  | .step j q _ qg prev _ old residual _ _ _ d _ _ =>
      (GaussianTriangularKernel.kernel old residual d, leaf L j q (qg 0)) :: prev.word

def Chain.initial {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : WordRecursion.State N → ℝ :=
  match chain with
  | .root q f => fun z => L.test q (projection f z)
  | .step _ _ _ _ prev _ _ _ _ _ _ _ _ _ => prev.initial

/-- Every original recursively changing finite test is exactly the
corresponding score-kernel word on one final observation space. -/
theorem Chain.test_eq_apply {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) :
    (fun z => UncutSmoothWords.test L k p (projection g z)) =
      TriangularScoreWords.apply chain.word chain.initial := by
  induction chain with
  | root p f => rfl
  | step k p f g prev ht old residual ho hr hc d hd hrange ih =>
    funext z
    change UncutSmoothWords.test L (k+1) p (projection g z) =
      leaf L k p (g 0) z * (GaussianTriangularKernel.kernel old residual d).action
        (TriangularScoreWords.apply prev.word prev.initial) z
    rw [← ih]
    exact lifted_score_step L k p f g ht ho hr hc d hd hrange z

theorem leaf_boundedSmooth (k : ℕ) (p : History P (k+1)) (i : Fin N) :
    BoundedSmooth (leaf L k p i) := by
  have h := (R.totalVariance_smooth.comp_right (EuclideanSpace.proj i)).sub
    (BoundedSmooth.const (R.reference ((carrier L k).nodeTime p,p.2.2)))
  exact (BoundedSmooth.const (1 / 2 : ℝ)).mul h

theorem Chain.fullTest_boundedSmooth {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) :
    BoundedSmooth (TriangularScoreWords.fullTest chain.word chain.initial) := by
  induction chain with
  | root p f => exact (L.test_uniform.boundedSmooth p).comp_right (projection f)
  | step k p f g prev ht old residual ho hr hc d hd hrange ih =>
    exact (leaf_boundedSmooth L k p (g 0)).mul ih

/-- Exact finite Gaussian product representation of the manuscript's
literal uncut recursive tests. Every covariance, direction, projection,
leaf and baseline is retained in the chain and its original full test. -/
theorem Chain.test_eq_integral {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) (htri : Triangular chain.word) (z : WordRecursion.State N) :
    UncutSmoothWords.test L k p (projection g z) =
      ∫ x : Fin chain.word.length → WordRecursion.State N × WordRecursion.State N,
        (∏ j, (chain.word.get j).1.score (x j)) *
          TriangularScoreWords.fullTest chain.word chain.initial
            (z + ∑ j, (chain.word.get j).1.shift (x j))
        ∂Measure.pi (fun j => (chain.word.get j).1.measure) := by
  obtain ⟨M, hM⟩ := chain.fullTest_boundedSmooth.norm_bound
  have h := word_eq_integral chain.word htri chain.initial
    chain.fullTest_boundedSmooth.smooth.continuous.measurable M
    (fun w => by simpa only [Real.norm_eq_abs] using hM w) z
  exact (congrFun chain.test_eq_apply z).trans h

end SHE.ProjectedUncutWord
