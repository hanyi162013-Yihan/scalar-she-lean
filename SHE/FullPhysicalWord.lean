module

public import SHE.PhysicalChainArrays
public import SHE.GaussianWordResidual

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures FixedOldScoreSupport
open scoped BigOperators Matrix.Norms.L2Operator
local instance fullPhysicalWord_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The literal full product: the original root and every original
centered coefficient leaf, including its full moving reference baseline. -/
def word (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N) (z : WordRecursion.State N) : ℝ :=
  initial L k p g z * ∏ j : Fin k, leaves L k p g j z

theorem word_measurable (k : ℕ) (g : Fin (n+k) → Fin N) :
    Measurable (fun p : History P k × WordRecursion.State N => word L k p.1 g p.2) :=
  (initial_measurable L k g).mul (Finset.measurable_prod Finset.univ (fun j _ => leaves_measurable L k g j))

theorem word_eq_centered (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N) (z : WordRecursion.State N) :
    word L k p g z = (1/2:ℝ)^k * FiniteCenteredProduct.test Finset.univ (initial L k p g)
      (fun j w => R.totalVariance (w (leafIndex k g j))) (baseline L k p) z := by
  simp only [word, leaves, FiniteCenteredProduct.test, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem fullTest_eq_product {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) (z : WordRecursion.State N) :
    TriangularScoreWords.fullTest chain.word (Chain.initial L chain) z =
      Chain.initial L chain z * ∏ j, chain.leaves j z := by
  induction chain with
  | root p f => simp only [Chain.word, TriangularScoreWords.fullTest, List.foldr_nil, Fin.prod_univ_zero, mul_one]
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    change leaf L k p (g 0) z * TriangularScoreWords.fullTest prev.word (Chain.initial L prev) z = _
    rw [ih, Fin.prod_univ_succ]
    change _ = Chain.initial L prev z * (leaf L k p (g 0) z * ∏ j, prev.leaves j z)
    ring

theorem fullTest_eq_word {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) :
    TriangularScoreWords.fullTest chain.word chain.initial = word L k p g := by
  funext z
  rw [fullTest_eq_product L chain z, chain_initial_eq L chain, chain_leaves_eq L chain]
  rfl

/-- Exact all-order representation of the actual recursive uncut test
using deterministic physical interval arrays. No measurable choice of a
proof-bearing chain occurs in either side of the identity. -/
theorem test_eq_weighted_average_ae (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k, ∀ z : WordRecursion.State (n+k),
      UncutSmoothWords.test L k p z =
        GaussianConvolution.gaussianAverage
          (∑ j, covariances L ((carrier L k).observations.observations p)
            (fun r => R.reference r - c r) k p j)
          (WeightedBorelAverage.average
            (Measure.pi (fun j => multivariateGaussian (0 : WordRecursion.State (n+k))
              (covariances L ((carrier L k).observations.observations p) c k p j)))
            (fun x => ∏ j, MeasurableGaussianScores.secondScore
              (covariances L ((carrier L k).observations.observations p) c k p j)
              (directions L ((carrier L k).observations.observations p) k p j) (x j))
            (fun x => ∑ j, x j) (word L k p (fun i => i))) z := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,hs,_,hphysical⟩ := hp
  intro z
  have h := chain.test_eq_pair_integral hs z
  obtain ⟨M,hM⟩ := chain.fullTest_boundedSmooth.norm_bound
  have he := GaussianWordResidual.pair_word_eq_residual_average chain.old chain.residual
    chain.residual_posSemidef chain.direction (TriangularScoreWords.fullTest chain.word chain.initial)
    chain.fullTest_boundedSmooth.smooth.continuous.measurable M
    (fun w => by simpa only [Real.norm_eq_abs] using hM w) z
  rw [he] at h
  rw [Physical.old_eq L _ c chain hphysical, Physical.residual_eq L _ c chain hphysical,
    Physical.direction_eq L _ c chain hphysical, fullTest_eq_word L chain] at h
  have hid : projection (fun i : Fin (n+k) => i) z = z := by ext i; rfl
  rwa [hid] at h

end SHE.PhysicalChainArrays
