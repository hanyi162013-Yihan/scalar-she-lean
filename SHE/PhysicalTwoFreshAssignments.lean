module

public import SHE.TwoFreshWholeWordAssignments
public import SHE.ChainAssignedRepresentation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
local instance physicalTwoFreshAssignments_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ}
variable (L:Level R X n)

def twoFreshMeasure (c:Domain→ℝ) (k:ℕ) (p:History X k)
    (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)):=
  (Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
    (covariances L ((carrier L k).observations.observations p) c k p j))).prod
      ((multivariateGaussian (0:WordRecursion.State (n+k)) Rnative).prod
        (multivariateGaussian (0:WordRecursion.State (n+k)) C))

def twoFreshWord (c:Domain→ℝ) (k:ℕ) (p:History X k) (second:Bool)
    (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)) (E V mean:WordRecursion.State (n+k))
    (choices:List (Fin k×Fin (k+1)))
    (z:(Fin k→WordRecursion.State (n+k))×(WordRecursion.State (n+k)×WordRecursion.State (n+k))):ℝ:=
  TwoFreshFullResidualMoments.word second
    (covariances L ((carrier L k).observations.observations p) c k p)
    (directions L ((carrier L k).observations.observations p) k p) Rnative C E V choices
    R.totalVariance (L.test (rootParameter k p)) (fun _:Unit=>mean)
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) ((),z)

/-- Supplied-chain physical attachment of the untouched TWO fresh score
carriers to the literal complete recursive word. The old intervals and
the original normalization are identified internally. -/
theorem two_fresh_score_average_of_chain (c:Domain→ℝ) {k:ℕ} {p:History X k}
    (chain:Chain L k p (fun i=>i))
    (hphysical:Physical L ((carrier L k).observations.observations p) c chain)
    (second:Bool) (Rnative C:MeasurableGeneralizedInverse.Mat (n+k))
    (hR:Rnative.PosSemidef) (hC:C.PosSemidef) (E V mean:WordRecursion.State (n+k))
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) Rnative).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range):
    let A:=covariances L ((carrier L k).observations.observations p) c k p
    let D:=directions L ((carrier L k).observations.observations p) k p
    WeightedBorelAverage.average (multivariateGaussian (0:WordRecursion.State (n+k)) C)
      (factor second C V) id
      (WeightedBorelAverage.average
        ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
          (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
        (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,secondScore (A j) (D j) (old j)))
        (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word L k p (fun i=>i))) mean=
      (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
        ∫z,twoFreshWord L c k p second Rnative C E V mean choices z
          ∂twoFreshMeasure L c k p Rnative C)).sum:=by
  intro A D
  have hA(j:Fin k):(A j).PosSemidef:=by
    rw [show A=chain.old from (Physical.old_eq L _ c chain hphysical).symm]
    exact chain.old_posSemidef j
  have hD(j:Fin k):D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range:=by
    rw [show A=chain.old from (Physical.old_eq L _ c chain hphysical).symm,
      show D=chain.direction from (Physical.direction_eq L _ c chain hphysical).symm]
    exact chain.assigned_direction_mem_range j
  obtain ⟨K,hK,hKF⟩:=L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩:=R.totalVariance_smooth.norm_bound
  have hF:Measurable (L.test (rootParameter k p)):=(L.test_uniform.smooth _).continuous.measurable
  have hFb(z:WordRecursion.State n):|L.test (rootParameter k p) z|≤K:=by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) z
  have hab(z:ℝ):|R.totalVariance z|≤M:=by simpa only [Real.norm_eq_abs] using hMa z
  let μoldR:=(Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
    (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative)
  let w:=GaussianFixedFirstAverage.weight Rnative E
    (fun old:Fin k→WordRecursion.State (n+k)=>∏j,secondScore (A j) (D j) (old j))
  let sh:=GaussianFixedFirstAverage.shift (fun old:Fin k→WordRecursion.State (n+k)=>∑j,old j)
  let raw:=VectorAssignmentIdentity.raw R.totalVariance (L.test (rootParameter k p))
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p)
  have hinner:WeightedBorelAverage.average μoldR w sh (fun z=>(1/2:ℝ)^k*raw z)=
      (fun z=>(1/2:ℝ)^k*WeightedBorelAverage.average μoldR w sh raw z):=by
    funext z
    exact WeightedBorelAverage.const_mul μoldR w sh raw ((1/2:ℝ)^k) z
  rw [word_eq_raw]
  change WeightedBorelAverage.average (multivariateGaussian (0:WordRecursion.State (n+k)) C)
    (factor second C V) id
    (WeightedBorelAverage.average μoldR w sh (fun z=>(1/2:ℝ)^k*raw z)) mean=_
  rw [hinner,WeightedBorelAverage.const_mul]
  congr 1
  exact TwoFreshWholeWordAssignments.score_average second A hA D hD Rnative C hR hC E V hE hV
    (List.finRange k) (List.nodup_finRange k) R.totalVariance
    R.totalVariance_smooth.smooth.continuous.measurable (L.test (rootParameter k p)) hF mean
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) hK hFb hab

/-- One original history event suffices for all native/fresh covariance
choices, score directions and current means; no parameter-dependent AE
event is substituted after evaluating the physical data. -/
theorem two_fresh_score_average_ae (c:Domain→ℝ) (hc:Measurable c)
    {ell:ℝ} (hell:0<ell) (hb:∀z,ell≤c z ∧ c z≤R.reference z)
    (hages:∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ:Measure X) [IsFiniteMeasure μ] (k:ℕ):
    ∀ᵐp∂CutoffWordHistories.historyMeasure R μ k,
      ∀(second:Bool) (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)),
      Rnative.PosSemidef→C.PosSemidef→
      ∀(E V mean:WordRecursion.State (n+k)),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) Rnative).range→
      V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range→
        let A:=covariances L ((carrier L k).observations.observations p) c k p
        let D:=directions L ((carrier L k).observations.observations p) k p
        WeightedBorelAverage.average (multivariateGaussian (0:WordRecursion.State (n+k)) C)
          (factor second C V) id
          (WeightedBorelAverage.average
            ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
              (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
            (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,secondScore (A j) (D j) (old j)))
            (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word L k p (fun i=>i))) mean=
          (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
            ∫z,twoFreshWord L c k p second Rnative C E V mean choices z
              ∂twoFreshMeasure L c k p Rnative C)).sum:=by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,_,_,hphysical⟩:=hp
  intro second Rnative C hR hC E V mean hE hV
  exact two_fresh_score_average_of_chain L c chain hphysical second Rnative C hR hC E V mean hE hV

end SHE.PhysicalChainArrays
