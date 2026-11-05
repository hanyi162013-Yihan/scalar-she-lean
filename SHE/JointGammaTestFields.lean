module

public import SHE.JointGammaAffine
public import SHE.FirstGammaTestFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000

namespace SHE.JointGammaTestFields
open Set MeasureTheory ControlledProfile SmoothCylinders UniformSmooth GaussianItoTest
open GaussianIncrement GaussianConvolution
open scoped NNReal ENNReal
local instance jointGammaTestFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance jointGammaTestFields_sigma : MeasurableSpace StoppedFourier.CircleL2 := borel _
local instance jointGammaTestFields_borel : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (htarget : ∀i,(b:ℝ)≤(Z i).target)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => JointGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "R" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)
attribute [local irreducible] JointGammaAffine.current FirstGammaAffine.reference

def value (p : Inputs) (t : ℝ) (z : FirstGammaAffine.Space n) : ℝ :=
  GaussianAffineFields.value (W p).path F (fun _=>L) (fun _=>0) t z-
    GaussianAffineFields.value (W p).path F (fun _=>R) (fun _=>0) t z

theorem value_apply (p : Inputs) (t : ℝ) (z : FirstGammaAffine.Space n) :
    value P Λ θ v b hvb Z htarget F p t z=backward (W p) F t (L z)-backward (W p) F t (R z) := by
  change gaussianAverage ((W p).path t).val F (L z+0)-
    gaussianAverage ((W p).path t).val F (R z+0)=_
  simp only [add_zero]
  rfl

def derivative (p : Inputs) (t : ℝ) (z : FirstGammaAffine.Space n) : ℝ :=
  GaussianEndpointAffine.derivative (W p) F (fun _=>L) (fun _=>0) (fun _=>0) (fun _=>0) t z-
    GaussianEndpointAffine.derivative (W p) F (fun _=>R) (fun _=>0) (fun _=>0) (fun _=>0) t z

include hF in
/-- The literal joint-current/frozen-reference test is admissible for
ordinary finite Ito through the zero-reserve endpoint. Its current map
is constant, so there is no corrected-current control drift. -/
theorem smoothTimeTest (p : Inputs) :
    LocalizedItoTest.SmoothTimeTest v b (value P Λ θ v b hvb Z htarget F p)
      (derivative P Λ θ v b hvb Z htarget F p) := by
  have hside (A : FirstGammaAffine.Space n→L[ℝ]WordRecursion.State n) :
      LocalizedItoTest.SmoothTimeTest (W p).left (W p).right
        (GaussianAffineFields.value (W p).path F (fun _=>A) (fun _=>0))
        (GaussianEndpointAffine.derivative (W p) F (fun _=>A) (fun _=>0) (fun _=>0) (fun _=>0)) := by
    have hh:=DampedEndpointAffine.smoothTimeTest (W p) (show 0≤(W p).left from v.coe_nonneg)
      hF (Λ:=0) (by norm_num) (0:ℝ) A 0 0 0
    have hl : DampedAffineGaussian.linear 0 0 A 0=(fun _=>A) := by
      funext t
      change A+_ • (0:FirstGammaAffine.Space n→L[ℝ]WordRecursion.State n)=A
      ext z i
      simp only [add_apply,smul_apply,zero_apply,PiLp.add_apply,PiLp.smul_apply,
        PiLp.zero_apply,smul_eq_mul,mul_zero,add_zero]
    have hdl : DampedAffineGaussian.linearDerivative 0 0
        (0:FirstGammaAffine.Space n→L[ℝ]WordRecursion.State n)=(fun _=>0) := by
      funext t
      change _ • (0:FirstGammaAffine.Space n→L[ℝ]WordRecursion.State n)=0
      ext z i
      simp only [smul_apply,zero_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero]
    have hs : DampedAffineGaussian.shift 0 0 (0:WordRecursion.State n) 0=(fun _=>0) := by
      funext t
      simp only [DampedAffineGaussian.shift,smul_zero,sub_zero]
    have hds : DampedAffineGaussian.shiftDerivative 0 0 (0:WordRecursion.State n)=(fun _=>0) := by
      funext t
      simp only [DampedAffineGaussian.shiftDerivative,smul_zero,neg_zero]
    rw [hl,hdl,hs,hds] at hh
    exact hh
  have hh:=(hside L).sub (hside R)
  convert hh using 1 <;> rfl

include hF in
theorem value_joint_measurable : Measurable
    (fun p : (Inputs×ℝ)×FirstGammaAffine.Space n=>value P Λ θ v b hvb Z htarget F p.1.1 p.1.2 p.2) := by
  have hm:=ControlledGaussianComparisonFields.base_value_joint_measurable P Λ θ v b hvb Z htarget F hF
  have hs:=(hm.comp (measurable_fst.prodMk ((L).measurable.comp measurable_snd))).sub
    (hm.comp (measurable_fst.prodMk ((R).measurable.comp measurable_snd)))
  convert hs using 1
  funext p
  exact value_apply P Λ θ v b hvb Z htarget F p.1.1 p.1.2 p.2

include hF in
theorem uniformSmooth : UniformBoundedSmooth
    (fun p : Inputs×ℝ=>value P Λ θ v b hvb Z htarget F p.1 p.2) := by
  have hb : UniformBoundedSmooth (fun p:Inputs×ℝ=>backward (W p.1) F p.2):=
    (UniformBoundedSmooth.fixed (P:=Inputs×ℝ) hF).average
      (fun p=>ProbabilityTheory.multivariateGaussian (0:WordRecursion.State n) ((W p.1).path p.2).val)
      (fun _=>inferInstance)
  convert (hb.comp_right L).sub (hb.comp_right R) using 1
  funext p z
  exact value_apply P Λ θ v b hvb Z htarget F p.1 p.2 z

attribute [local irreducible] value derivative
set_option backward.isDefEq.respectTransparency true in
include hF in
theorem gradient_joint_measurable : Measurable
    (fun p:Inputs×(ℝ×FirstGammaAffine.Space n)=>fderiv ℝ
      (value P Λ θ v b hvb Z htarget F p.1 p.2.1) p.2.2) := by
  have hd : ∀p:Inputs×ℝ,Differentiable ℝ (value P Λ θ v b hvb Z htarget F p.1 p.2):=
    fun p=>(uniformSmooth P Λ θ v b hvb Z htarget F hF).smooth p |>.differentiable (by simp)
  have hm:=MeasurableDerivatives.fderiv_measurable (n:=(n+n)+(n+n)) (G:=ℝ)
    (F:=fun p:Inputs×ℝ=>value P Λ θ v b hvb Z htarget F p.1 p.2)
    (value_joint_measurable P Λ θ v b hvb Z htarget F hF) hd
  exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

include hF in
theorem value_parameter_continuous (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) (t : ℝ) :
    Continuous (fun p:Inputs×FirstGammaAffine.Space n=>value P Λ θ v b hvb Z htarget F p.1 t p.2) := by
  have hc:=ControlledReferenceCovariance.backward_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t
  have hs:=(hc.comp (continuous_fst.prodMk ((L).continuous.comp continuous_snd))).sub
    (hc.comp (continuous_fst.prodMk ((R).continuous.comp continuous_snd)))
  convert hs using 1
  funext p
  exact value_apply P Λ θ v b hvb Z htarget F p.1 t p.2

end SHE.JointGammaTestFields
