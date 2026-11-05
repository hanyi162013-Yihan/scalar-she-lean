module

public import SHE.GaussianComparisonItoTest
public import SHE.ControlledReferenceCovariance
public import SHE.MeasurableDerivatives
public import SHE.GaussianScoreKernel
public import SHE.VariableObservations

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.ControlledGaussianComparisonFields
open Set MeasureTheory ProbabilityTheory StoppedFourier ControlledProfile GaussianItoTest GaussianConvolution
open SmoothCylinders UniformSmooth GaussianContinuity
open scoped NNReal ENNReal
local instance controlledGaussianComparisonFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledGaussianComparisonFields_sigma : MeasurableSpace CircleL2 := borel _
local instance controlledGaussianComparisonFields_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (htarget : ∀ i,(b:ℝ)≤(Z i).target)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p

def value (p : Inputs) (t : ℝ) (z : WordRecursion.State (n+n)) : ℝ := GaussianComparisonItoTest.value (W p) F t z

def derivative (p : Inputs) (t : ℝ) (z : WordRecursion.State (n+n)) : ℝ := GaussianComparisonItoTest.derivative (W p) F t z

include hF

theorem regular (p : Inputs) : GaussianItoTest.RegularTest v b
    (value P Λ θ v b hvb Z htarget F p) (derivative P Λ θ v b hvb Z htarget F p) :=
  GaussianComparisonItoTest.regular (W p) F hF

/-- One all-order derivative packet covers every original past pair and
all reserve times. Its bounds are independent of the selected past data. -/
theorem uniformSmooth : UniformBoundedSmooth
    (fun p : Inputs×ℝ=>value P Λ θ v b hvb Z htarget F p.1 p.2) := by
  have hs0 := (UniformBoundedSmooth.fixed (P:=Inputs×ℝ) hF).average
    (fun p : Inputs×ℝ=>multivariateGaussian (0:WordRecursion.State n) ((W p.1).path p.2).val)
    (fun _=>inferInstance)
  have hs : UniformBoundedSmooth (fun p : Inputs×ℝ=>GaussianItoTest.backward (W p.1) F p.2) := hs0
  exact (hs.comp_right (FiniteComparisonTest.left n)).sub (hs.comp_right (FiniteComparisonTest.right n))

theorem base_value_joint_measurable : Measurable
    (fun p : (Inputs×ℝ)×WordRecursion.State n=>backward (W p.1.1) F p.1.2 p.2) := by
  let S : VariableObservations.Family (Inputs×ℝ) n:=VariableObservations.Family.fixed Z
  have hcm : Measurable (fun p : (Inputs×ℝ)×(ℝ×HeatCircle)=>(p.1.1,p.2)):=
    measurable_fst.fst.prodMk measurable_snd
  have hcoef := (ControlledReferenceWindows.coefficient_measurable P Λ θ v).comp hcm
  have hq : Measurable (fun p : Inputs×ℝ=>ClippedCovariance.clip v b p.2) :=
    (ClippedCovariance.continuous_clip v b).measurable.comp measurable_snd
  have hmat:=S.covariance_measurable hcoef hq measurable_const
    (fun p=>(ClippedCovariance.clip_mem (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb) p.2).2)
  let M := fun p : (Inputs×ℝ)×WordRecursion.State n=>((W p.1.1).path p.1.2).val
  have hM : Measurable M := by
    convert hmat.comp measurable_fst using 1
    funext p
    rfl
  have htest : Measurable (fun p : ((Inputs×ℝ)×WordRecursion.State n)×WordRecursion.State n=>F (p.1.2+p.2)) :=
    hF.smooth.continuous.measurable.comp (measurable_fst.snd.add measurable_snd)
  have hh:=(htest.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=GaussianScoreKernel.gaussianKernel M hM)).measurable
  exact hh

theorem value_joint_measurable : Measurable
    (fun p : (Inputs×ℝ)×WordRecursion.State (n+n)=>value P Λ θ v b hvb Z htarget F p.1.1 p.1.2 p.2) := by
  have hl := (base_value_joint_measurable P Λ θ v b hvb Z htarget F hF).comp
    (measurable_fst.prodMk ((FiniteComparisonTest.left n).measurable.comp measurable_snd))
  have hr := (base_value_joint_measurable P Λ θ v b hvb Z htarget F hF).comp
    (measurable_fst.prodMk ((FiniteComparisonTest.right n).measurable.comp measurable_snd))
  exact hl.sub hr

set_option backward.isDefEq.respectTransparency true in
theorem gradient_joint_measurable : Measurable
    (fun p : Inputs×(ℝ×WordRecursion.State (n+n))=>fderiv ℝ
      (value P Λ θ v b hvb Z htarget F p.1 p.2.1) p.2.2) := by
  have hdiff : ∀ p : Inputs×ℝ,Differentiable ℝ (value P Λ θ v b hvb Z htarget F p.1 p.2) :=
    fun p=>(uniformSmooth P Λ θ v b hvb Z htarget F hF).smooth p |>.differentiable (by simp)
  have hm:=MeasurableDerivatives.fderiv_measurable (n:=n+n) (G:=ℝ)
    (F:=fun p : Inputs×ℝ=>value P Λ θ v b hvb Z htarget F p.1 p.2)
    (value_joint_measurable P Λ θ v b hvb Z htarget F hF)
    hdiff
  have hmap : Measurable (fun p : Inputs×(ℝ×WordRecursion.State (n+n)) => ((p.1,p.2.1),p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hh := hm.comp hmap
  exact hh

variable (hΛ : 0≤Λ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
include hΛ hsmall in
theorem value_parameter_continuous (t : ℝ) : Continuous
    (fun p : Inputs×WordRecursion.State (n+n)=>value P Λ θ v b hvb Z htarget F p.1 t p.2) := by
  have hc:=ControlledReferenceCovariance.backward_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t
  have hl:=hc.comp (continuous_fst.prodMk ((FiniteComparisonTest.left n).continuous.comp continuous_snd))
  have hr:=hc.comp (continuous_fst.prodMk ((FiniteComparisonTest.right n).continuous.comp continuous_snd))
  unfold value GaussianComparisonItoTest.value
  exact hl.sub hr

include hΛ hsmall in
theorem gradient_parameter_continuous (t : ℝ) (z : WordRecursion.State (n+n)) :
    Continuous (fun p : Inputs=>fderiv ℝ (value P Λ θ v b hvb Z htarget F p t) z) := by
  have hs : UniformBoundedSmooth (fun p : Inputs=>value P Λ θ v b hvb Z htarget F p t) := by
    have hh:=uniformSmooth P Λ θ v b hvb Z htarget F hF
    refine ⟨fun p=>hh.smooth (p,t),fun k=>?_⟩
    obtain ⟨B,hB0,hB⟩:=hh.bounds k
    exact ⟨B,hB0,fun p z=>hB (p,t) z⟩
  obtain ⟨B,hB0,hB⟩:=hs.fderiv.fderiv.norm_bound
  have hc:=ParameterSmoothContinuity.continuous_fderiv
    (E:=WordRecursion.State (n+n)) (G:=ℝ)
    (fun p : Inputs=>value P Λ θ v b hvb Z htarget F p t)
    (value_parameter_continuous P Λ θ v b hvb Z htarget F hF hΛ hsmall t)
    (fun p=>(hs.smooth p).of_le (by simp)) hB0 hB
  have hh:=hc.comp (continuous_id.prodMk (continuous_const (y:=z)))
  exact hh

end SHE.ControlledGaussianComparisonFields
