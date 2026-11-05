module

public import SHE.VectorAssignmentIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.ProjectedUncutWord
open MeasureTheory CutoffWordLevel CutoffWordHistories
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable {L : CutoffWordLevel.Level R P n}

theorem Chain.assigned_direction_mem_range {k : ℕ} {p : History P k} {g : Fin (n+k)→Fin N}
    (chain : Chain L k p g) (j : Fin k) :
    chain.direction j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (chain.old j)).range := by
  induction chain with
  | root p f => exact Fin.elim0 j
  | step k p f g prev ht old residual ho hr hc d hd hrg ih =>
    exact Fin.cases hrg (fun i => ih i) j

end SHE.ProjectedUncutWord

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
open scoped BigOperators
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def assignedProduct (k : ℕ) (p : History P k)
    (choices : List (Fin k×Fin (k+1))) (mean residual : WordRecursion.State (n+k))
    (x : Fin k→WordRecursion.State (n+k)) : ℝ :=
  VectorControlledRoot.value choices 0 (L.test (rootParameter k p)) mean
    (rootSelector k (fun i => i)) (x,residual)*
      ∏ j,ControlledAssignedLeaf.leaf choices j.succ R.totalVariance mean
        (leafIndex k (fun i => i) j) (baseline L k p j) (x,residual)

def assignedSum (k : ℕ) (p : History P k) (mean residual : WordRecursion.State (n+k))
    (x : Fin k→WordRecursion.State (n+k)) : ℝ :=
  ((assignments (m:=k+1) (List.finRange k)).map (fun choices => assignedProduct L k p choices mean residual x)).sum

theorem word_eq_raw (k : ℕ) (p : History P k) :
    word L k p (fun i => i)=fun z => (1/2:ℝ)^k*
      VectorAssignmentIdentity.raw R.totalVariance (L.test (rootParameter k p))
        (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p) z := by
  funext z
  simp only [word,initial,leaves,VectorAssignmentIdentity.raw,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

/-- Literal physical oldAverage expanded into the exact canonical
root/rough blocks. No chain, covariance-range or Gaussian-compatibility
premise remains; every original centered baseline and factor 1/2 stays. -/
theorem oldAverage_assignment_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,∀ mean residual : WordRecursion.State (n+k),
      oldAverage L c k p (mean+residual)=(1/2:ℝ)^k*
        ∫ x,(∏ j,MeasurableGaussianScores.secondScore
          (covariances L ((carrier L k).observations.observations p) c k p j)
          (directions L ((carrier L k).observations.observations p) k p j) (x j))*
          assignedSum L k p mean residual x
          ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k))
            (covariances L ((carrier L k).observations.observations p) c k p j)) := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,_,_,hphysical⟩ := hp
  let Z := (carrier L k).observations.observations p
  have hA (j : Fin k) : (covariances L Z c k p j).PosSemidef := by
    rw [←Physical.old_eq L Z c chain hphysical]
    exact chain.old_posSemidef j
  have hD (j : Fin k) : directions L Z k p j∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (covariances L Z c k p j)).range := by
    rw [←Physical.old_eq L Z c chain hphysical,←Physical.direction_eq L Z c chain hphysical]
    exact chain.assigned_direction_mem_range j
  obtain ⟨K,hK,hKF⟩ := L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩ := R.totalVariance_smooth.norm_bound
  have hF : Measurable (L.test (rootParameter k p)) :=
    (L.test_uniform.smooth _).continuous.measurable
  have hFb (z : WordRecursion.State n) : |L.test (rootParameter k p) z|≤K := by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) z
  have hab (z : ℝ) : |R.totalVariance z|≤M := by simpa only [Real.norm_eq_abs] using hMa z
  intro mean residual
  have hh := VectorAssignmentIdentity.old_average_eq (covariances L Z c k p) hA
    (directions L Z k p) hD (List.finRange k) (List.nodup_finRange k)
    R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable
    (L.test (rootParameter k p)) hF (rootSelector k (fun i => i))
    (leafIndex k (fun i => i)) (baseline L k p) hK hFb hab mean residual
  change WeightedBorelAverage.average _ _ _ (word L k p (fun i => i)) (mean+residual)=_
  rw [word_eq_raw,WeightedBorelAverage.const_mul]
  apply congrArg (fun z : ℝ => (1/2:ℝ)^k*z)
  convert! hh using 1

/-- The actual terminal first-score representation with the full
canonical old assignment sum substituted. The terminal and residual
Gaussian variables remain untouched, as required for the sharp mean row. -/
theorem terminal_first_score_assignments_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ lo : ℝ,0≤lo → lo<(carrier L k).terminal p →
      ∀ (v : CircleL2) (z : WordRecursion.State (n+k)),
      let Z := (carrier L k).observations.observations p
      let hi := (carrier L k).terminal p
      let A := intervalCovariance Z c lo hi
      let B := intervalCovariance Z (fun r => R.reference r-c r) lo hi
      let d := PhysicalFirstScore.terminalDirection Z lo v
      fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference Z lo hi)
        (UncutSmoothWords.test L k p)) z d=
        ∫ terminal,∫ residual,((1/2:ℝ)^k*
          ∫ old,(∏ j,MeasurableGaussianScores.secondScore (covariances L Z c k p j)
            (directions L Z k p j) (old j))*assignedSum L k p z (terminal+residual) old
            ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k))
              (covariances L Z c k p j)))*MeasurableGaussianScores.firstScore A d terminal
          ∂multivariateGaussian 0 (B+∑ j,covariances L Z (fun r => R.reference r-c r) k p j)
          ∂multivariateGaussian 0 A := by
  filter_upwards [terminal_first_score_ae L c hc hell hb hages μ k,
    oldAverage_assignment_ae L c hc hell hb hages μ k] with p ht ha
  intro lo hlo hgap v z
  dsimp only
  rw [ht lo hlo hgap v z]
  apply integral_congr_ae
  apply ae_of_all
  intro terminal
  apply integral_congr_ae
  apply ae_of_all
  intro residual
  dsimp only
  rw [show z+terminal+residual=z+(terminal+residual) by abel,ha z (terminal+residual)]

end SHE.PhysicalChainArrays
