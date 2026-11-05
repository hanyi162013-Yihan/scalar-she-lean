module

public import SHE.ScoreChainSupport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ProjectedUncutWord
open Set MeasureTheory ProbabilityTheory WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers GaussianCoordinates TriangularScoreWords
open scoped BigOperators
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable {L : CutoffWordLevel.Level R P n}

def Chain.old {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Fin k → MeasurableGeneralizedInverse.Mat N :=
  match chain with
  | .root _ _ => Fin.elim0
  | .step _ _ _ _ prev _ old _ _ _ _ _ _ _ => Fin.cases old prev.old

def Chain.residual {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Fin k → MeasurableGeneralizedInverse.Mat N :=
  match chain with
  | .root _ _ => Fin.elim0
  | .step _ _ _ _ prev _ _ residual _ _ _ _ _ _ => Fin.cases residual prev.residual

def Chain.direction {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Fin k → WordRecursion.State N :=
  match chain with
  | .root _ _ => Fin.elim0
  | .step _ _ _ _ prev _ _ _ _ _ _ d _ _ => Fin.cases d prev.direction

def Chain.leaves {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Fin k → WordRecursion.State N → ℝ :=
  match chain with
  | .root _ _ => Fin.elim0
  | .step j q _ qg prev _ _ _ _ _ _ _ _ _ => Fin.cases (leaf L j q (qg 0)) prev.leaves

theorem Chain.word_eq_ofFn {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) :
    chain.word = List.ofFn (fun j : Fin k =>
      (GaussianTriangularKernel.kernel (chain.old j) (chain.residual j) (chain.direction j), chain.leaves j)) := by
  induction chain with
  | root p f => rfl
  | step k p f g prev ht old residual ho hr hc d hd hrange ih =>
    simp only [Chain.word, List.ofFn_succ, Chain.old, Chain.residual,
      Chain.direction, Chain.leaves, Fin.cases_zero, Fin.cases_succ, ih]

theorem Chain.old_posSemidef {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) (j : Fin k) : (chain.old j).PosSemidef := by
  induction chain with
  | root p f => exact Fin.elim0 j
  | step k p f g prev ht old residual ho hr hc d hd hrange ih =>
    exact Fin.cases ho (fun i => ih i) j

theorem Chain.residual_posSemidef {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) (j : Fin k) : (chain.residual j).PosSemidef := by
  induction chain with
  | root p f => exact Fin.elim0 j
  | step k p f g prev ht old residual ho hr hc d hd hrange ih =>
    exact Fin.cases hr (fun i => ih i) j

/-- The actual original test as a product of its independent physical
old/residual Gaussian pairs, with exactly one old score per insertion. -/
theorem Chain.test_eq_pair_integral {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) (hs : chain.CoordinateSupport) (z : WordRecursion.State N) :
    UncutSmoothWords.test L k p (projection g z) =
      ∫ x : Fin k → WordRecursion.State N × WordRecursion.State N,
        (∏ j, MeasurableGaussianScores.secondScore (chain.old j) (chain.direction j) (x j).1) *
          TriangularScoreWords.fullTest chain.word chain.initial
            (z + ∑ j, ((x j).1 + (x j).2))
        ∂Measure.pi (fun j => (multivariateGaussian (0 : WordRecursion.State N) (chain.old j)).prod
          (multivariateGaussian 0 (chain.residual j))) := by
  have ht := chain.triangular_of_coordinateSupport hs
  have ha := apply_eq_actions_fullTest chain.word ht chain.initial
  have he : chain.word.map Prod.fst = List.ofFn (fun j : Fin k =>
      GaussianTriangularKernel.kernel (chain.old j) (chain.residual j) (chain.direction j)) := by
    rw [chain.word_eq_ofFn, List.map_ofFn]
    rfl
  have hpoint := (congrFun chain.test_eq_apply z).trans (congrFun ha z)
  rw [he] at hpoint
  obtain ⟨M,hM⟩ := chain.fullTest_boundedSmooth.norm_bound
  have hf := actions_eq_integral k
    (fun j => GaussianTriangularKernel.kernel (chain.old j) (chain.residual j) (chain.direction j))
    (TriangularScoreWords.fullTest chain.word chain.initial)
    chain.fullTest_boundedSmooth.smooth.continuous.measurable M
    (fun w => by simpa only [Real.norm_eq_abs] using hM w) z
  exact hpoint.trans hf

end SHE.ProjectedUncutWord
