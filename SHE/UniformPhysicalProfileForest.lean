module

public import SHE.UniformPhysicalScoreForest
public import SHE.UniformOldIntervalScores
public import SHE.PhysicalTerminalAssignments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianCoordinates FixedOldScoreSupport OldIntervalCovariance PhysicalChainArrays
  MeasurableGaussianScores ScoreProjectionEnergy StoppedGaussianFeatures PhysicalParentGeometry OrderedHeatForests
open scoped BigOperators
local instance uniformPhysicalProfileForest_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X ι : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The full physical parent-forest event can be selected BEFORE an
arbitrary uncountable family of reference profiles. It is constructed
from the actual constant-floor recursive chain and then covariance
order; all adaptive centers keep the genuine earlier-frame Fubini. -/
theorem uniform_all_profiles_forest_ae {ell M : ℝ} (hell : 0<ell)
    (hfloor : ∀ p,ell ≤ R.reference p)
    (c : ι→Domain→ℝ) (hc : ∀ a,Measurable (c a))
    (hb : ∀ a p,ell ≤ c a p ∧ c a p ≤ M)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ a,
      (∀ j : Fin k,directions L ((carrier L k).observations.observations p) k p j∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ)
          (covariances L ((carrier L k).observations.observations p) (c a) k p j)).range) ∧
      ∀ hp : StrictHistory L k p,SmallHistory L (uniformHorizon n) k p→
        scoreProduct L ((carrier L k).observations.observations p) (c a) k p ≤ 
          timeWeight L ell (uniformConstant n) k p*parentDensity 2 (by norm_num) k
            (fun i=>((carrier L k).observations.observations p i).target)
            (carrier_orderedTimes L hages k p hp)
            (fun i=>((carrier L k).observations.observations p i).center) := by
  have hfb (p : Domain) : ell ≤ (fun _=>ell) p ∧ (fun _=>ell) p ≤ R.reference p := ⟨le_rfl,hfloor p⟩
  filter_upwards [uniform_actual_score_forest_ae L (fun _=>ell) measurable_const hell hfb hages μ k,
    exists_chain_ae L (fun _=>ell) measurable_const hell hfb hages μ k] with p hforest hchain
  obtain ⟨chain,_,_,hphysical⟩ := hchain
  let Z := (carrier L k).observations.observations p
  have hZ := RecursiveScoreSupport.carrier_ages L hages k p
  have hrange0 (j : Fin k) : directions L Z k p j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (covariances L Z (fun _=>ell) k p j)).range := by
    rw [←Physical.old_eq L Z _ chain hphysical,←Physical.direction_eq L Z _ chain hphysical]
    exact chain.assigned_direction_mem_range j
  have hcompare (a : ι) (j : Fin k) := UniformOldIntervalScores.interval_range_and_score
    (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) hZ
    (lower L k p j) (upper L k p j) (c a) (hc a) hell (hb a) (directions L Z k p j) (hrange0 j)
  intro a
  refine ⟨fun j=>(hcompare a j).1,?_⟩
  intro hp hsmall
  have hle : scoreProduct L Z (c a) k p ≤ scoreProduct L Z (fun _=>ell) k p := by
    apply Finset.prod_le_prod₀
    · intro j _
      apply scoreVariance_nonneg _ (hcompare a j).1
      exact OldIntervalCovariance.covariance_posSemidef _ _ _ hZ (c a) (hc a)
        (fun r=>⟨hell.le.trans (hb a r).1,(hb a r).2⟩) _ _
    · intro j _
      exact (hcompare a j).2
  exact hle.trans (hforest hp hsmall)

end SHE.PhysicalScoreChain
