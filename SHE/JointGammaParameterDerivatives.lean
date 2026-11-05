module

public import SHE.JointGammaTestFields
public import SHE.CovarianceCoefficientContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.JointGammaParameterDerivatives
open Set MeasureTheory ControlledProfile SmoothCylinders UniformSmooth GaussianItoTest
open GaussianConvolution GaussianTaylorAverage
open scoped NNReal ENNReal
local instance jointGammaParameterDerivatives_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance jointGammaParameterDerivatives_sigma : MeasurableSpace StoppedFourier.CircleL2 := borel _
local instance jointGammaParameterDerivatives_borel : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ)
variable (v b : ℝ≥0) (hvb : v≤b) {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) {F : WordRecursion.State n→ℝ} (hF : BoundedSmooth F)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "G" => JointGammaTestFields.value P Λ θ v b hvb Z htarget F
local notation "dG" => JointGammaTestFields.derivative P Λ θ v b hvb Z htarget F

include hF hΛ in
theorem fixed_uniformSmooth (t : ℝ) : UniformBoundedSmooth (fun p : Inputs=>G p t) := by
  have hh:=JointGammaTestFields.uniformSmooth P Λ θ v b hvb Z htarget F hF
  refine ⟨fun p=>hh.smooth (p,t),fun k=>?_⟩
  obtain ⟨B,hB0,hB⟩:=hh.bounds k
  exact ⟨B,hB0,fun p z=>hB (p,t) z⟩

include hF hΛ hsmall in
theorem gradient_parameter_continuous (t : ℝ) : Continuous
    (fun p : Inputs×FirstGammaAffine.Space n=>fderiv ℝ (G p.1 t) p.2) := by
  have hs:=fixed_uniformSmooth P hΛ θ v b hvb Z htarget hF t
  obtain ⟨B,hB0,hB⟩:=hs.fderiv.fderiv.norm_bound
  exact ParameterSmoothContinuity.continuous_fderiv _
    (JointGammaTestFields.value_parameter_continuous P Λ θ v b hvb Z htarget F hF hΛ hsmall t)
    (fun p=>(hs.smooth p).of_le (by simp)) hB0 hB

include hF hΛ hsmall in
theorem hessian_parameter_continuous (t : ℝ) : Continuous
    (fun p : Inputs×FirstGammaAffine.Space n=>GaussianTaylor.hessian (G p.1 t) p.2) :=
  ParameterSmoothContinuity.continuous_hessian _
    (JointGammaTestFields.value_parameter_continuous P Λ θ v b hvb Z htarget F hF hΛ hsmall t)
    (fixed_uniformSmooth P hΛ θ v b hvb Z htarget hF t)

include hF hΛ hsmall in
theorem derivative_parameter_continuous {t : ℝ} (ht : t<(b:ℝ)) :
    Continuous (fun p : Inputs×FirstGammaAffine.Space n=>dG p.1 t p.2) := by
  have hD (i j : Fin n) : Continuous (fun p : Inputs=>
      CovarianceMatrix.densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v p) Z t i j) :=
    CovarianceCoefficientContinuity.continuous_density (ControlledReferenceWindows.coefficient P Λ θ v)
      (ControlledReferenceWindows.coefficient_section_measurable P Λ θ v)
      (ControlledReferenceWindows.coefficient_inputs_continuous P Λ θ v hΛ hsmall)
      Z P.upper_nonneg ht htarget (fun p x=>ControlledReferenceWindows.coefficient_abs_bound P Λ θ v p (t,x)) i j
  have hb:=ControlledReferenceCovariance.backward_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t
  have hs : UniformBoundedSmooth (fun p : Inputs=>backward (W p) F t) :=
    (UniformBoundedSmooth.fixed (P:=Inputs) hF).average
      (fun p=>ProbabilityTheory.multivariateGaussian (0:WordRecursion.State n) ((W p).path t).val) (fun _=>inferInstance)
  obtain ⟨B,hB0,hB⟩:=hs.fderiv.fderiv.norm_bound
  have hg:=ParameterSmoothContinuity.continuous_fderiv _ hb
    (fun p=>(hs.smooth p).of_le (by simp)) hB0 hB
  have hH:=ControlledReferenceCovariance.hessian_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t
  have hside (L DL : FirstGammaAffine.Space n→L[ℝ]WordRecursion.State n) : Continuous
      (fun p : Inputs×FirstGammaAffine.Space n=>GaussianEndpointAffine.derivative (W p.1) F
        (fun _=>L) (fun _=>DL) (fun _=>0) (fun _=>0) t p.2) := by
    have hmap : Continuous (fun p : Inputs×FirstGammaAffine.Space n=>(p.1,L p.2)):=
      continuous_fst.prodMk (L.continuous.comp continuous_snd)
    have hgr:=hg.comp hmap
    have hhe:=hH.comp hmap
    have hcov : Continuous (fun p : Inputs×FirstGammaAffine.Space n=>
        -(1/2:ℝ)*covarianceAction (CovarianceMatrix.densityMatrix
          (ControlledReferenceWindows.coefficient P Λ θ v p.1) Z t)
          (GaussianTaylor.hessian (backward (W p.1) F t) (L p.2))) := by
      apply Continuous.const_mul
      unfold covarianceAction
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact ((hD i j).comp continuous_fst).mul ((hhe.clm_apply continuous_const).clm_apply continuous_const)
    have hh:=hcov.add (hgr.clm_apply (DL.continuous.comp continuous_snd))
    convert hh using 1
    funext p
    simp only [GaussianEndpointAffine.derivative,GaussianAffineFields.mean,add_zero,
      GaussianItoTest.backward,ControlledReferenceWindows.window,Function.comp_def,Pi.add_apply]
    try rfl
  have hh:=(hside (JointGammaAffine.current n Λ θ (fun i=>(Z i).target))
      (0)).sub
    (hside (FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)) 0)
  convert hh using 1
  funext p
  rfl

end SHE.JointGammaParameterDerivatives
