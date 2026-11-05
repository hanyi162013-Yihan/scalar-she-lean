module

public import SHE.ActualBaselineAssignments
public import SHE.ActualCovarianceMarkFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ActualBaselineMarkFields
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement GaussianConvolution
  StoppedFourier StoppedGaussianFeatures WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredControlledLaw HistoryProductMeasure PhysicalParentGeometry
open scoped BigOperators NNReal
local instance actualBaselineMarkFields_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {Ω X W : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R X n)

/-- The literal fixed-old erased test remains jointly Borel in all
original histories and the current mean. -/
theorem omitted_old_average_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ) (j0 : Fin k) :
    Measurable (fun p : History X k×WordRecursion.State (n+k)=>
      WeightedBorelAverage.average
        (Measure.pi (fun j=>multivariateGaussian (0 : WordRecursion.State (n+k))
          (covariances L ((carrier L k).observations.observations p.1) c k p.1 j)))
        (fun x=>∏ j,MeasurableGaussianScores.secondScore
          (covariances L ((carrier L k).observations.observations p.1) c k p.1 j)
          (directions L ((carrier L k).observations.observations p.1) k p.1 j) (x j)) (fun x=>∑ j,x j)
        (FiniteCenteredProduct.test (Finset.univ.erase j0) (initial L k p.1 (fun i=>i))
          (fun j z=>R.totalVariance (z (leafIndex k (fun i=>i) j))) (baseline L k p.1)) p.2) := by
  let F : (History X k×WordRecursion.State (n+k))×WordRecursion.State (n+k)→ℝ := fun z=>
    FiniteCenteredProduct.test (Finset.univ.erase j0) (initial L k z.1.1 (fun i=>i))
      (fun j w=>R.totalVariance (w (leafIndex k (fun i=>i) j))) (baseline L k z.1.1) z.2
  have hF : Measurable F := by
    change Measurable (fun z : (History X k×WordRecursion.State (n+k))×WordRecursion.State (n+k)=>
      initial L k z.1.1 (fun i=>i) z.2 *∏ j∈Finset.univ.erase j0,
        (R.totalVariance (z.2 (leafIndex k (fun i=>i) j))-baseline L k z.1.1 j))
    have hroot : Measurable (fun z : (History X k×WordRecursion.State (n+k))×WordRecursion.State (n+k)=>
        initial L k z.1.1 (fun i=>i) z.2) := by
      convert! (initial_measurable L k (fun i=>i)).comp
        (measurable_fst.fst.prodMk measurable_snd) using 1
    refine hroot.mul ?_
    apply Finset.measurable_prod
    intro j _
    exact (R.totalVariance_smooth.smooth.continuous.measurable.comp
      (((EuclideanSpace.proj (𝕜:=ℝ) (leafIndex k (fun i=>i) j)).continuous.measurable).comp measurable_snd)).sub
        ((baseline_measurable L k j).comp measurable_fst.fst)
  convert! GaussianProductAverageFields.weighted_average_measurable
    (X:=History X k×WordRecursion.State (n+k))
    (fun p j=>covariances L ((carrier L k).observations.observations p.1) c k p.1 j)
    (fun j=>(old_covariances_measurable L c hc k j).comp measurable_fst)
    (fun p j=>directions L ((carrier L k).observations.observations p.1) k p.1 j)
    (fun j=>(old_directions_measurable L k j).comp measurable_fst) F hF Prod.snd measurable_snd using 1

/-- Globally Borel extension of the actual baseline leg, agreeing with
its literal full-residual Gaussian average whenever q<terminal. -/
def point (c : Domain→ℝ) (k : ℕ) (q : ℝ) (db : Fin k→ℝ)
    (m : WordRecursion.State (n+k)) (p : History X k) : ℝ :=
  if q<(carrier L k).terminal p then baselineMark L c k p q db m else 0

theorem point_of_active (c : Domain→ℝ) (k : ℕ) (q : ℝ) (db : Fin k→ℝ)
    (m : WordRecursion.State (n+k)) (p : History X k) (hq : q<(carrier L k).terminal p) :
    point L c k q db m p=baselineMark L c k p q db m := by
  simp only [point,ite_eq_left hq]

/-- Covariance rank, original history, profile derivative vector,
current state and current time may all vary dependently. -/
theorem point_variable_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ)
    (p : W→History X k) (hp : Measurable p) (q : W→ℝ) (hq : Measurable q)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m)
    (db : W→Fin k→ℝ) (hdb : Measurable db) :
    Measurable (fun w=>point L c k (q w) (db w) (m w) (p w)) := by
  classical
  have hA := (ActualCovarianceMarkFields.cappedResidual_measurable L c hc k).comp (hp.prodMk hq)
  have hterm (j0 : Fin k) : Measurable (fun w=>db w j0*(1/2:ℝ)^k*
      gaussianAverage (ActualCovarianceMarkFields.cappedResidual L c k (p w) (q w))
        (WeightedBorelAverage.average
          (Measure.pi (fun j=>multivariateGaussian (0 : WordRecursion.State (n+k))
            (covariances L ((carrier L k).observations.observations (p w)) c k (p w) j)))
          (fun x=>∏ j,MeasurableGaussianScores.secondScore
            (covariances L ((carrier L k).observations.observations (p w)) c k (p w) j)
            (directions L ((carrier L k).observations.observations (p w)) k (p w) j) (x j)) (fun x=>∑ j,x j)
          (FiniteCenteredProduct.test (Finset.univ.erase j0) (initial L k (p w) (fun i=>i))
            (fun j z=>R.totalVariance (z (leafIndex k (fun i=>i) j))) (baseline L k (p w)))) (m w)) := by
    have hF := (omitted_old_average_measurable L c hc k j0).comp
      ((hp.comp measurable_fst).prodMk ((hm.comp measurable_fst).add measurable_snd))
    have hG := (hF.stronglyMeasurable.integral_kernel_prod_right'
      (κ:=GaussianScoreKernel.gaussianKernel
        (fun w=>ActualCovarianceMarkFields.cappedResidual L c k (p w) (q w)) hA)).measurable
    convert! (((measurable_pi_apply j0).comp hdb).mul_const ((1/2:ℝ)^k)).mul hG using 1
  have hG := (Finset.measurable_sum Finset.univ (fun j _=>hterm j)).neg
  have hs : MeasurableSet {w : W | q w<(carrier L k).terminal (p w)} :=
    measurableSet_lt hq ((carrier L k).terminal_measurable.comp hp)
  convert! hG.ite hs (measurable_const (a:=(0:ℝ))) using 1
  funext w
  simp only [point,baselineMark,omittedAverage]
  split_ifs with hw
  · simp only [Pi.neg_apply,ActualCovarianceMarkFields.cappedResidual,min_eq_left hw.le,mul_assoc]
  · rfl
  all_goals infer_instance

theorem spatial_variable_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ)
    (root : W→X) (hroot : Measurable root) (times : W→Fin k→ℝ) (htimes : Measurable times)
    (q : W→ℝ) (hq : Measurable q)
    (m : W×History X k→WordRecursion.State (n+k)) (hm : Measurable m)
    (db : W×History X k→Fin k→ℝ) (hdb : Measurable db) :
    Measurable (fun w=>∫ x : Fin k→HeatCircle,
      point L c k (q w) (db (w,separated k (root w,times w,x)))
        (m (w,separated k (root w,times w,x))) (separated k (root w,times w,x))
          ∂Measure.pi (fun _=>haarAddCircle)) := by
  let h : W×(Fin k→HeatCircle)→History X k := fun z=>separated k (root z.1,times z.1,z.2)
  have hh : Measurable h := (separated_measurable k).comp
    ((hroot.comp measurable_fst).prodMk ((htimes.comp measurable_fst).prodMk measurable_snd))
  have hm' : Measurable (fun z : W×(Fin k→HeatCircle)=>m (z.1,h z)) := by
    convert! hm.comp (measurable_fst.prodMk hh) using 1
  have hdb' : Measurable (fun z : W×(Fin k→HeatCircle)=>db (z.1,h z)) := by
    convert! hdb.comp (measurable_fst.prodMk hh) using 1
  have hf := point_variable_measurable L c hc k h hh (fun z=>q z.1) (hq.comp measurable_fst)
    (fun z=>m (z.1,h z)) hm' (fun z=>db (z.1,h z)) hdb'
  convert! (hf.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _ : Fin k=>haarAddCircle))).measurable using 1

end SHE.ActualBaselineMarkFields
