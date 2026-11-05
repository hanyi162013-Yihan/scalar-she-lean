module

public import SHE.ControlledRootGeometry
public import SHE.ControlledFamilyFrontFields
public import SHE.BoundedGaussianSums
public import SHE.UnconditionalCovarianceSums
public import SHE.TranslatedProfileRowEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ControlledFrontRootSums
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers SmoothCylinders UniformSmooth PhysicalChainArrays PhysicalScoreChain
  RootSmoothSums CoveredControlledLaw
open scoped NNReal BigOperators
local instance controlledFrontRootSums_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFrontRootSums_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFrontRootSums_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : ℕ→X→WordRecursion.State n→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
variable (hFm : ∀ j,Measurable (fun z : X×WordRecursion.State n=>F j z.1 z.2))
local notation "B"=>(fun j=>ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop (F j) (hF j) (hFm j))

/-- Finite-root linearity of the actual Gaussian-front value. The
covariance, full recursive baselines, and original-stop current vector
remain exactly the same for every summand. -/
theorem actualValue_sum (s : Finset ℕ) (p : ControlledProfile.Inputs) (k : ℕ) (h : History X k)
    (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop
      (rootSum F s) (rootSum_uniform F hF s) (rootSum_measurable F hFm s) p k h q U D θ=
      ∑ j∈s,ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop
        (F j) (hF j) (hFm j) p k h q U D θ := by
  classical
  let M:=ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop
    (F 0) (hF 0) (hFm 0) p k h q U D θ
  let C:=WordRecursion.covariance (ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb p).reference
    ((carrier (B 0 (θ,p)) k).observations.observations h) q ((carrier (B 0 (θ,p)) k).terminal h)
  have he (G : X→WordRecursion.State n→ℝ) (hg : UniformBoundedSmooth G)
      (hgm : Measurable (fun z : X×WordRecursion.State n=>G z.1 z.2)) :
      ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop G hg hgm p k h q U D θ=
        GaussianConvolution.gaussianAverage C
          (UncutSmoothWords.test (RootFiniteSums.withRoot (B 0 (θ,p)) G hg hgm) k h) M := by
    unfold ControlledFamilyActualTransfer.actualValue
    rw [ControlledRootGeometry.observations_eq P A hA Λ v b hvb Z htarget hstop
        G (F 0) hg (hF 0) hgm (hFm 0),
      ControlledRootGeometry.terminal_eq P A hA Λ v b hvb Z htarget hstop
        G (F 0) hg (hF 0) hgm (hFm 0),
      ControlledRootGeometry.mean_eq P A hA Λ v b hvb Z htarget hstop
        G (F 0) hg (hF 0) hgm (hFm 0)]
    rfl
  rw [he (rootSum F s) (rootSum_uniform F hF s) (rootSum_measurable F hFm s)]
  simp_rw [he]
  let G:=fun j=>UncutSmoothWords.test (RootFiniteSums.band (B 0 (θ,p)) F hF hFm j) k h
  have ht:=RootFiniteSums.test_sum (B 0 (θ,p)) F hF hFm s k h
  rw [show UncutSmoothWords.test
      (RootFiniteSums.withRoot (B 0 (θ,p)) (rootSum F s)
        (rootSum_uniform F hF s) (rootSum_measurable F hFm s)) k h=
        (fun z=>∑ j∈s,G j z) by
    convert! ht using 1
    ext z
    simp only [Finset.sum_apply,G]]
  choose Cj hCj using fun j=>(ActualMeanKernel.test_boundedSmooth
    (RootFiniteSums.band (B 0 (θ,p)) F hF hFm j) k h).norm_bound
  simpa only [Finset.sum_apply,G,RootFiniteSums.band] using congrFun (GaussianConvolution.gaussianAverage_finite C G
    (fun j=>(ActualMeanKernel.test_boundedSmooth _ k h).smooth.continuous.measurable)
    Cj (fun j z=>by simpa only [Real.norm_eq_abs] using hCj j z) s) M

theorem activeValue_sum (s : Finset ℕ) (p : ControlledProfile.Inputs) (k : ℕ) (h : History X k)
    (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop
      (rootSum F s) (rootSum_uniform F hF s) (rootSum_measurable F hFm s) p k h q U D θ=
      ∑ j∈s,ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop
        (F j) (hF j) (hFm j) p k h q U D θ := by
  classical
  unfold ControlledFamilyFrontFields.activeValue
  rw [ControlledRootGeometry.terminal_eq P A hA Λ v b hvb Z htarget hstop
    (rootSum F s) (F 0) (rootSum_uniform F hF s) (hF 0) (rootSum_measurable F hFm s) (hFm 0)]
  simp_rw [ControlledRootGeometry.terminal_eq P A hA Λ v b hvb Z htarget hstop
    (F _) (F 0) (hF _) (hF 0) (hFm _) (hFm 0)]
  by_cases ha : (v:ℝ)≤q ∧ q<(carrier (B 0 (0,p)) k).terminal h
  · simp only [if_pos ha]
    exact actualValue_sum P A hA Λ v b hvb Z htarget hstop F hF hFm s p k h q U D θ
  · simp only [if_neg ha,Finset.sum_const_zero]

end SHE.ControlledFrontRootSums

