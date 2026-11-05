module

public import SHE.RootPhysicalGeometry
public import SHE.BoundedPhysicalWord

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootFiniteSums
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  SmoothCylinders UniformSmooth PhysicalScoreChain PhysicalChainArrays RootSmoothSums GaussianConvolution
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n N : ℕ}
variable (L : Level R X n)

theorem oldAverage_withRoot (G : X→WordRecursion.State n→ℝ) (hG : UniformBoundedSmooth G)
    (hGm : Measurable (fun z : X×WordRecursion.State n=>G z.1 z.2))
    (c : StoppedGaussianFeatures.Domain→ℝ) (k : ℕ) (p : History X k) :
    oldAverage (withRoot L G hG hGm) c k p=
      WeightedBorelAverage.average
        (Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
          (covariances L ((carrier L k).observations.observations p) c k p j)))
        (fun x=>∏ j,MeasurableGaussianScores.secondScore
          (covariances L ((carrier L k).observations.observations p) c k p j)
          (directions L ((carrier L k).observations.observations p) k p j) (x j))
        (fun x=>∑ j,x j) (word (withRoot L G hG hGm) k p (fun i=>i)) := by
  unfold oldAverage
  rw [RootFiniteGeometry.observations_eq L G hG hGm k p,
    RootPhysicalGeometry.covariances_eq L G hG hGm,
    RootPhysicalGeometry.directions_eq L G hG hGm]

variable (F : ℕ→X→WordRecursion.State n→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
  (hFm : ∀ j,Measurable (fun z : X×WordRecursion.State n=>F j z.1 z.2))
local notation "B"=>band L F hF hFm
local notation "S"=>sumLevel L F hF hFm

/-- Literal finite-root additivity of the original product word,
including every original moving coefficient baseline. -/
theorem physical_word_sum (s : Finset ℕ) (k : ℕ) (p : History X k)
    (g : Fin (n+k)→Fin N) (z : WordRecursion.State N) :
    word (S s) k p g z=∑ j∈s,word (B j) k p g z := by
  simp only [sumLevel,band,RootPhysicalGeometry.word_withRoot,rootSum,Finset.sum_mul]

/-- The actual fixed-old score average is linear in finite root cutoffs.
The Gaussian laws, score directions and every centered rough baseline
remain identical. All Gaussian product integrals are justified. -/
theorem oldAverage_sum (s : Finset ℕ) (c : StoppedGaussianFeatures.Domain→ℝ)
    (k : ℕ) (p : History X k) : oldAverage (S s) c k p=∑ j∈s,oldAverage (B j) c k p := by
  classical
  simp only [sumLevel,band,oldAverage_withRoot L]
  let ν:=Measure.pi (fun j : Fin k=>multivariateGaussian (0:WordRecursion.State (n+k))
    (covariances L ((carrier L k).observations.observations p) c k p j))
  let w:=fun x : Fin k→WordRecursion.State (n+k)=>∏ j,MeasurableGaussianScores.secondScore
    (covariances L ((carrier L k).observations.observations p) c k p j)
    (directions L ((carrier L k).observations.observations p) k p j) (x j)
  let shift:=fun x : Fin k→WordRecursion.State (n+k)=>∑ j,x j
  have hw : Integrable w ν:=old_weight_integrable L c k p
  have hs : Measurable shift:=Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j)
  have hword : word (S s) k p (fun i=>i)=fun z=>∑ j∈s,word (B j) k p (fun i=>i) z:=
    funext (physical_word_sum L F hF hFm s k p (fun i=>i))
  choose M hM using fun j=>(word_boundedSmooth (B j) k p (fun i=>i)).norm_bound
  funext z
  simp only [Finset.sum_apply]
  change WeightedBorelAverage.average ν w shift (word (S s) k p (fun i=>i)) z=
    ∑ j∈s,WeightedBorelAverage.average ν w shift (word (B j) k p (fun i=>i)) z
  rw [hword]
  exact WeightedBorelAverage.finset_sum s ν w hw shift hs
    (fun j=>word (B j) k p (fun i=>i))
    (fun j _=>(word_boundedSmooth (B j) k p (fun i=>i)).smooth.continuous.measurable)
    M (fun j _ x=>by simpa only [Real.norm_eq_abs] using hM j x) z
end SHE.RootFiniteSums
