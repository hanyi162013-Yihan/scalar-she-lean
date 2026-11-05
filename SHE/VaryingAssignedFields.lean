module

public import SHE.FullResidualPointwiseOffset
public import SHE.GaussianProductAverageFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.VaryingAssignedFields
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks GaussianJointScoreMoments
  MeasurableGaussianScores GaussianDependentScores GaussianScoreKernel
open scoped BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

/-- Variable baselines remain Borel after the actual assigned block and
foreign-coordinate suppressions, including the empty-block case. -/
theorem leaf_measurable (choices : List (Fin r×Fin m)) (factor : Fin m)
    (a : ℝ→ℝ) (ha : Measurable a) (mean : Ω→State n) (hm : Measurable mean)
    (i : Fin n) (baseline : Ω→ℝ) (hb : Measurable baseline) :
    Measurable (fun z : Ω×((Fin r→State n)×State n)=>
      ControlledAssignedLeaf.leaf choices factor a (mean z.1) i (baseline z.1) z.2) := by
  by_cases hblock : block choices factor=[]
  · have he : (fun z : Ω×((Fin r→State n)×State n)=>
        ControlledAssignedLeaf.leaf choices factor a (mean z.1) i (baseline z.1) z.2)=
        (fun z=>a ((mean z.1) i+((∑ j,suppress (suppressed choices factor) z.2.1 j)+z.2.2) i)-baseline z.1) :=
      funext (fun z=>ControlledAssignedLeaf.leaf_empty choices factor hblock a (mean z.1) i (baseline z.1) z.2)
    rw [he]
    have hs : Measurable (fun z : Ω×((Fin r→State n)×State n)=>
        (∑ j,suppress (suppressed choices factor) z.2.1 j)+z.2.2) :=
      (Finset.measurable_sum Finset.univ (fun j _=>(measurable_pi_apply j).comp
        ((measurable_suppress _).comp measurable_snd.fst))).add measurable_snd.snd
    exact (ha.comp ((((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable).comp
      (hm.comp measurable_fst)).add (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable).comp hs))).sub
        (hb.comp measurable_fst)
  · have he : (fun z : Ω×((Fin r→State n)×State n)=>
        ControlledAssignedLeaf.leaf choices factor a (mean z.1) i (baseline z.1) z.2)=
        (fun z=>ControlledAssignedLeaf.leaf choices factor a (mean z.1) i 0 z.2) := by
      funext z
      rw [ControlledAssignedLeaf.leaf_nonempty choices factor hblock a (mean z.1) i (baseline z.1),
        ControlledAssignedLeaf.leaf_nonempty choices factor hblock a (mean z.1) i 0]
    rw [he]
    exact ParametricAssignedMoments.leaf_measurable choices factor a ha mean hm i 0

/-- Actual old/product/residual Gaussian kernels may vary and change
rank with every original probability parameter. The full assigned word
average is Borel, with no constant-covariance identification. -/
theorem average_measurable
    (A : Ω→Fin r→MeasurableGeneralizedInverse.Mat n) (hA : ∀ j,Measurable (fun ω=>A ω j))
    (D : Ω→Fin r→State n) (hD : ∀ j,Measurable (fun ω=>D ω j))
    (B : Ω→MeasurableGeneralizedInverse.Mat n) (hB : Measurable B)
    (E : Ω→State n) (hE : Measurable E) (second : Bool)
    (choices : List (Fin r×Fin (m+1))) (a : ℝ→ℝ) (ha : Measurable a)
    (F : State d→ℝ) (hF : Measurable F) (mean : Ω→State n) (hm : Measurable mean)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Ω→Fin m→ℝ)
    (hbase : ∀ j,Measurable (fun ω=>baseline ω j)) :
    Measurable (fun ω=>∫ x,FullResidualAssignedMoments.word second (A ω) (D ω) (B ω) (E ω)
      choices a F (fun _ : Unit=>mean ω) g leaf (baseline ω) ((),x)
      ∂(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A ω j))).prod
        (multivariateGaussian (0 : State n) (B ω))) := by
  have hold (j : Fin r) : Measurable (fun z : Ω×((Fin r→State n)×State n)=>
      secondScore (A z.1 j) (D z.1 j) (z.2.1 j)) := by
    have hy : Measurable (fun z : Ω×((Fin r→State n)×State n)=>z.2.1 j) :=
      (measurable_pi_apply j).comp measurable_snd.fst
    have hp : Measurable (fun z : Ω×((Fin r→State n)×State n)=>((A z.1 j,D z.1 j),z.2.1 j)) :=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk hy
    convert! (secondScore_measurable (n:=n)).comp hp using 1

  have hfresh : Measurable (fun z : Ω×((Fin r→State n)×State n)=>
      factor second (B z.1) (E z.1) z.2.2) := by
    cases second
    · convert! firstScore_measurable.comp
        (((hB.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd.snd) using 1
    · convert! secondScore_measurable.comp
        (((hB.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd.snd) using 1
  have hroot := ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g
  have hleaves := Finset.measurable_prod Finset.univ
    (fun j _=>leaf_measurable choices j.succ a ha mean hm (leaf j) (fun ω=>baseline ω j) (hbase j))
  have hword : Measurable (fun z : Ω×((Fin r→State n)×State n)=>
      FullResidualAssignedMoments.word second (A z.1) (D z.1) (B z.1) (E z.1) choices a F
        (fun _ : Unit=>mean z.1) g leaf (baseline z.1) ((),z.2)) := by
    convert! (((Finset.measurable_prod Finset.univ (fun j _=>hold j)).mul hfresh).mul hroot).mul hleaves using 1
  let κold := FiniteKernelProduct.kernel r (fun j=>gaussianKernel (fun ω=>A ω j) (hA j))
  let κ := κold.prod (gaussianKernel B hB)
  have hh := (hword.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  convert! hh using 1
  funext ω
  rw [show κ ω=(Measure.pi (fun j=>multivariateGaussian (0 : State n) (A ω j))).prod
      (multivariateGaussian (0 : State n) (B ω)) by
    dsimp only [κ]
    rw [Kernel.prod_apply,FiniteKernelProduct.kernel_apply]
    rfl]

end SHE.VaryingAssignedFields
