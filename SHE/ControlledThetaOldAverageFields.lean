module

public import SHE.ControlledThetaCovarianceFields
public import SHE.GaussianProductAverageFields
public import SHE.ActualCovarianceMarkFields
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHE.ControlledThetaOldAverageFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
  SmoothCylinders UniformSmooth GaussianContinuity PhysicalChainArrays ControlledReferenceLevel FiniteCenteredProduct
open scoped NNReal
local instance controlledThetaOldAverageFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaOldAverageFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaOldAverageFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Every centered subset of original native leaves is jointly Borel in
the ACTUAL theta-reference family and all dependent histories/means. -/
theorem centered_test_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ) (s : Finset (Fin k))
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) :
    Measurable (fun w=>test s (initial (Base (p w)) k (h w) (fun i=>i))
      (fun j z=>A (z (leafIndex k (fun i=>i) j))) (baseline (Base (p w)) k (h w)) (m w)) := by
  have hroot : Measurable (fun w=>initial (Base (p w)) k (h w) (fun i=>i) (m w)) := by
    have hg:=hFm.comp (((rootParameter_measurable k).comp hh).prodMk
      ((GaussianCoordinates.projection (rootSelector k (fun i=>i))).measurable.comp hm))
    exact hg
  have hbase (j : Fin k) : Measurable (fun w=>baseline (Base (p w)) k (h w) j) := by
    have hlo:=((lower_measurable (Base (0,(0,0))) k j).comp hh)
    have hsp:=((space_measurable k j).comp hh)
    have hc:=ControlledThetaWordFields.coefficient_joint_measurable P Λ v
    have hmap : Measurable (fun w=>(p w,(lower (Base (0,(0,0))) k (h w) j,space k (h w) j))) :=
      hp.prodMk (hlo.prodMk hsp)
    have hg:=hc.comp hmap
    convert hg using 1
    funext w
    unfold baseline
    rw [ControlledThetaPhysicalGeometry.lower_eq P A hA Λ v b hvb Z htarget hstop F hF hFm (p w) (0,(0,0)) k (h w)]
    rfl
  unfold test
  refine hroot.mul (Finset.measurable_prod s (fun j _=>?_))
  exact (hA.smooth.continuous.measurable.comp
    ((EuclideanSpace.proj (𝕜:=ℝ) (leafIndex k (fun i=>i) j)).continuous.measurable.comp hm)).sub (hbase j)

/-- Genuine moving-family full old-score average for any jointly Borel
test, including all changing-rank physical old matrices and directions. -/
theorem weighted_average_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c)
    (G : W×WordRecursion.State (n+k)→ℝ) (hG : Measurable G)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) :
    Measurable (fun w=>WeightedBorelAverage.average
      (Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
        (covariances (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w))
          (fun r=>c (w,r)) k (h w) j)))
      (fun x=>∏ j,MeasurableGaussianScores.secondScore
        (covariances (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w))
          (fun r=>c (w,r)) k (h w) j)
        (directions (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w)) k (h w) j) (x j))
      (fun x=>∑ j,x j) (fun z=>G (w,z)) (m w)) := by
  exact GaussianProductAverageFields.weighted_average_measurable _
    (fun j=>ControlledThetaCovarianceFields.covariances_variable_measurable
      P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh c hc j) _
    (fun j=>ControlledThetaCovarianceFields.directions_variable_measurable
      P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh j) G hG m hm

theorem old_average_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) :
    Measurable (fun w=>oldAverage (Base (p w)) (fun r=>c (w,r)) k (h w) (m w)) := by
  have htest:=centered_test_variable_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k Finset.univ
    (fun z : W×WordRecursion.State (n+k)=>p z.1) (hp.comp measurable_fst)
    (fun z=>h z.1) (hh.comp measurable_fst) Prod.snd measurable_snd
  have hw : Measurable (fun z : W×WordRecursion.State (n+k)=>word (Base (p z.1)) k (h z.1) (fun i=>i) z.2) := by
    convert htest.const_mul ((1/2:ℝ)^k) using 1
    funext z
    exact word_eq_centered _ _ _ _ _
  exact weighted_average_variable_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm
    k p hp h hh c hc (fun z=>word (Base (p z.1)) k (h z.1) (fun i=>i) z.2) hw m hm

end SHE.ControlledThetaOldAverageFields
