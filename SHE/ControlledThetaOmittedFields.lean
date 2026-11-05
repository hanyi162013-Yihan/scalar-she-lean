module

public import SHE.ControlledThetaOldAverageFields
public import SHE.ActualBaselineMarkFields
public import SHE.GaussianProductAverageFields
public import SHE.ActualCovarianceMarkFields
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHE.ControlledThetaOmittedFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
  SmoothCylinders UniformSmooth GaussianContinuity PhysicalChainArrays ControlledReferenceLevel FiniteCenteredProduct
open scoped NNReal
local instance controlledThetaOmittedFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaOmittedFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaOmittedFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The actual erased-leaf Gaussian average is jointly Borel when the
law time is capped at the original history terminal. Every reference,
past input, history, mean and law time may depend on the same parameter. -/
theorem capped_omitted_average_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) (j0 : Fin k) :
    Measurable (fun w=>omittedAverage (Base (p w)) (fun r=>c (w,r)) k (h w)
      (min (q w) ((carrier (Base (p w)) k).terminal (h w))) j0 (m w)) := by
  classical
  have hAr:=ControlledThetaCovarianceFields.capped_residual_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq c hc
  have hc' : Measurable (fun z : (W×WordRecursion.State (n+k))×StoppedGaussianFeatures.Domain=>c (z.1.1,z.2)) :=
    hc.comp (measurable_fst.fst.prodMk measurable_snd)
  have htest:=ControlledThetaOldAverageFields.centered_test_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k (Finset.univ.erase j0)
    (fun z : (W×WordRecursion.State (n+k))×WordRecursion.State (n+k)=>p z.1.1)
    (hp.comp measurable_fst.fst) (fun z=>h z.1.1) (hh.comp measurable_fst.fst) Prod.snd measurable_snd
  have hmean : Measurable (fun z : W×WordRecursion.State (n+k)=>m z.1+z.2):=
    (hm.comp measurable_fst).add measurable_snd
  have hav:=ControlledThetaOldAverageFields.weighted_average_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : W×WordRecursion.State (n+k)=>p z.1) (hp.comp measurable_fst)
    (fun z=>h z.1) (hh.comp measurable_fst) (fun z=>c (z.1.1,z.2)) hc'
    (fun z=>test (Finset.univ.erase j0) (initial (Base (p z.1.1)) k (h z.1.1) (fun i=>i))
      (fun j w=>A (w (leafIndex k (fun i=>i) j))) (baseline (Base (p z.1.1)) k (h z.1.1)) z.2)
    htest (fun z=>m z.1+z.2) hmean
  have hgauss:=(hav.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=GaussianScoreKernel.gaussianKernel _ hAr)).measurable
  have hcgauss:=hgauss.const_mul ((1/2:ℝ)^k)
  convert hcgauss using 1
  funext w
  simp only [omittedAverage,ActualCovarianceMarkFields.cappedResidual]
  rfl

/-- On the actual law window the same statement concerns the literal
uncapped omitted average, with no reference-dependent exceptional set. -/
theorem omitted_average_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) (j0 : Fin k)
    (hwindow : ∀ w,q w≤(carrier (Base (p w)) k).terminal (h w)) :
    Measurable (fun w=>omittedAverage (Base (p w)) (fun r=>c (w,r)) k (h w) (q w) j0 (m w)) := by
  have he:=capped_omitted_average_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq c hc m hm j0
  simpa only [min_eq_left (hwindow _)] using he

end SHE.ControlledThetaOmittedFields
