module

public import SHE.PhysicalTerminalAssignments
public import SHE.GaussianFreshSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2
open scoped BigOperators
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

def terminalAssignedWord (c : Domain→ℝ) (k : ℕ) (p : History X k) (lo : ℝ)
    (v : CircleL2) (mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) :
    ((Fin (k+1)→WordRecursion.State (n+k))×WordRecursion.State (n+k))→ℝ :=
  let Z := (carrier L k).observations.observations p
  WindowFirstScoreWord.word R.totalVariance flags
    (GaussianFreshFraction.covariances (intervalCovariance Z c lo ((carrier L k).terminal p))
      (covariances L Z c k p))
    (Fin.cons (PhysicalFirstScore.terminalDirection Z lo v) (directions L Z k p))
    (liftChoices choices) (L.test (rootParameter k p)) mean
    (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p)

def terminalAssignedMeasure (c : Domain→ℝ) (k : ℕ) (p : History X k) (lo : ℝ) :
    Measure ((Fin (k+1)→WordRecursion.State (n+k))×WordRecursion.State (n+k)) :=
  let Z := (carrier L k).observations.observations p
  (Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k))
    (GaussianFreshFraction.covariances (intervalCovariance Z c lo ((carrier L k).terminal p))
      (covariances L Z c k p) j))).prod
    (multivariateGaussian 0 (intervalCovariance Z (fun r => R.reference r-c r) lo ((carrier L k).terminal p)+
      ∑ j,covariances L Z (fun r => R.reference r-c r) k p j))

/-- The literal recursive terminal derivative is bounded by the exact
finite sum of full Gaussian assigned-word norms. Integrability and
singular-covariance range conditions are derived from the physical chain
and ellipticity, so no abstract word-representation premise is required. -/
theorem terminal_first_score_norm_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ lo : ℝ,0≤lo → lo<(carrier L k).terminal p →
      ∀ (v : CircleL2) (z : WordRecursion.State (n+k)),
      (∀ choices,MemLp (terminalAssignedWord L c k p lo v z choices) 2
        (terminalAssignedMeasure L c k p lo)) ∧
      |fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) lo ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z
        (PhysicalFirstScore.terminalDirection ((carrier L k).observations.observations p) lo v)|≤
        (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
          normTwo (terminalAssignedMeasure L c k p lo) (terminalAssignedWord L c k p lo v z choices))).sum := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k,
    terminal_first_score_assignments_ae L c hc hell hb hages μ k] with p hp ht
  obtain ⟨chain,_,_,hphysical⟩ := hp
  intro lo hlo hgap v z
  let Z := (carrier L k).observations.observations p
  let A := covariances L Z c k p
  let D := directions L Z k p
  let T := intervalCovariance Z c lo ((carrier L k).terminal p)
  let d := PhysicalFirstScore.terminalDirection Z lo v
  let B := intervalCovariance Z (fun r => R.reference r-c r) lo ((carrier L k).terminal p)+
    ∑ j,covariances L Z (fun r => R.reference r-c r) k p j
  letI : IsProbabilityMeasure (terminalAssignedMeasure L c k p lo) := by
    dsimp only [terminalAssignedMeasure]
    infer_instance
  have hZ : ∀ i,(Z i).stop≤(Z i).target := RecursiveScoreSupport.carrier_ages L hages k p
  have hcb (r : Domain) : ell≤c r ∧ c r≤R.upper :=
    ⟨(hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have hA (j : Fin k) : (A j).PosSemidef := by
    rw [show A=chain.old from (Physical.old_eq L Z c chain hphysical).symm]
    exact chain.old_posSemidef j
  have hD (j : Fin k) : D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range := by
    rw [show A=chain.old from (Physical.old_eq L Z c chain hphysical).symm,
      show D=chain.direction from (Physical.direction_eq L Z c chain hphysical).symm]
    exact chain.assigned_direction_mem_range j
  have hT : T.PosSemidef := PhysicalFirstScore.interval_posSemidef Z hZ c hc
    (fun r => ⟨hell.le.trans (hcb r).1,(hcb r).2⟩) lo ((carrier L k).terminal p)
  have hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range :=
    PhysicalFirstScore.terminalDirection_mem_range Z hlo hgap ((carrier L k).stops_after p) hZ c hc hell hcb v
  obtain ⟨K,hK,hKF⟩ := L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩ := R.totalVariance_smooth.norm_bound
  have hF : Measurable (L.test (rootParameter k p)) :=
    (L.test_uniform.smooth _).continuous.measurable
  have hFb (w : WordRecursion.State n) : |L.test (rootParameter k p) w|≤K := by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) w
  have hab (w : ℝ) : |R.totalVariance w|≤M := by simpa only [Real.norm_eq_abs] using hMa w
  have hm (choices : List (Fin k×Fin (k+1))) :
      MemLp (terminalAssignedWord L c k p lo v z choices) 2 (terminalAssignedMeasure L c k p lo) := by
    exact GaussianFreshWord.word_memLp flags (GaussianFreshFraction.covariances T A)
      (Fin.cases hT hA) (Fin.cons d D) (Fin.cases hd hD) B (liftChoices choices)
      R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable (L.test (rootParameter k p)) hF
      z (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p) hK hFb hab
  refine ⟨hm,?_⟩
  rw [ht lo hlo hgap v z]
  have he := GaussianFreshSum.nested_sum_eq T A B d D (assignments (m:=k+1) (List.finRange k))
    R.totalVariance (L.test (rootParameter k p)) z (rootSelector k (fun i => i))
    (leafIndex k (fun i => i)) (baseline L k p) (fun choices _ => (hm choices).integrable (by norm_num))
  have hf :
      (∫ terminal,∫ residual,((1/2:ℝ)^k*
        ∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
          assignedSum L k p z (terminal+residual) old
          ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k)) (A j)))*
        MeasurableGaussianScores.firstScore T d terminal
        ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T)=
      (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
        ∫ x,terminalAssignedWord L c k p lo v z choices x ∂terminalAssignedMeasure L c k p lo)).sum := by
    have he' :
        (∫ terminal,∫ residual,(∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
          assignedSum L k p z (terminal+residual) old
          ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k)) (A j)))*
          MeasurableGaussianScores.firstScore T d terminal
          ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T)=
        ((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
          ∫ x,terminalAssignedWord L c k p lo v z choices x ∂terminalAssignedMeasure L c k p lo)).sum := by
      convert! he using 1
    rw [←he',←integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro terminal
    dsimp only
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun residual => by dsimp only [assignedSum,assignedProduct];ring)
  change |(∫ terminal,∫ residual,((1/2:ℝ)^k*
    ∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
      assignedSum L k p z (terminal+residual) old
      ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k)) (A j)))*
      MeasurableGaussianScores.firstScore T d terminal
      ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T)|≤_
  rw [hf,abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^k)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact GaussianFreshSum.abs_sum_le _ _ _ (fun choices _ =>
    DependentWordAssembly.abs_integral_le_normTwo _ (hm choices))

end SHE.PhysicalChainArrays
