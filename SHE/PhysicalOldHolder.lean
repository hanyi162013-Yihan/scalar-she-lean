module
public import SHE.PhysicalLeafHolder
public import SHE.MatrixHolderScore

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion GaussianIncrement
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates PhysicalScoreChain
open scoped BigOperators
local instance physicalOldHolder_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ} (L:Level R X n)

def wordHolderCost (A B H K β:ℝ)(k:ℕ)(p:History X k)(d:WordRecursion.State (n+k)):ℝ:=
  (1+B+(A+R.upper)/2)^(k+1)*
    (K+H/2*(∑j:Fin k,|d (leafIndex k (fun i=>i) j)|^β))

theorem wordHolderCost_nonneg {A B H K β:ℝ}(hA:0≤A)(hB:0≤B)(hH:0≤H)(hK:0≤K)
    (k:ℕ)(p:History X k)(d:WordRecursion.State (n+k)):
    0≤wordHolderCost (R:=R) A B H K β k p d:=by
  unfold wordHolderCost
  have hRU:=R.upper_nonneg
  positivity

/-- The actual full fixed-old average has a coefficient-index-uniform
directional Hölder modulus. Only its genuine old-score absolute mass
and original root/coefficient Hölder constants occur. -/
theorem oldAverage_directional_holder (c:StoppedGaussianFeatures.Domain→ℝ)
    {A B H K β:ℝ}(hA:0≤A)(hB:0≤B)(hH:0≤H)(hK:0≤K)
    (ha:∀z,|R.totalVariance z|≤A)(hroot:∀p z,|L.test p z|≤B)
    (hh:∀s t,|R.totalVariance s-R.totalVariance t|≤H*|s-t|^β)
    (k:ℕ)(p:History X k)(d:WordRecursion.State (n+k))
    (hr:∀x s t,|initial L k p (fun i=>i) (x+s • d)-
      initial L k p (fun i=>i) (x+t • d)|≤K*|s-t|^β)
    (z:WordRecursion.State (n+k))(s t:ℝ):
    |oldAverage L c k p (z+s • d)-oldAverage L c k p (z+t • d)|≤
      (wordHolderCost (R:=R) A B H K β k p d*oldAbsoluteMass L c k p)*|s-t|^β:=by
  let Z:=(carrier L k).observations.observations p
  let ν:=Measure.pi (fun j:Fin k=>multivariateGaussian (0:WordRecursion.State (n+k)) (covariances L Z c k p j))
  let w:=fun x:Fin k→WordRecursion.State (n+k)=>∏j,MeasurableGaussianScores.secondScore
    (covariances L Z c k p j) (directions L Z k p j) (x j)
  let shift:=fun x:Fin k→WordRecursion.State (n+k)=>∑j,x j
  have hw:Integrable w ν:=old_weight_integrable L c k p
  have hs:Measurable shift:=Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j)
  have hm:Measurable (word L k p (fun i=>i)):=(word_boundedSmooth L k p _).smooth.continuous.measurable
  exact WeightedBorelAverage.directional_holder ν w hw shift hs (word L k p (fun i=>i)) hm
    (B*((A+R.upper)/2)^k) (word_cap L hA hB ha hroot k p _) d
    (word_directional_holder L hA hB hH hK ha hroot hh k p (fun i=>i) d hr) z s t

end SHE.PhysicalChainArrays
