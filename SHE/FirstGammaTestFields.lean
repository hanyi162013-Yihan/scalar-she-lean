module

public import SHE.FirstGammaGaussianTest
public import SHE.ControlledGaussianComparisonFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.FirstGammaTestFields
open Set MeasureTheory ControlledProfile SmoothCylinders UniformSmooth GaussianItoTest
open GaussianIncrement GaussianConvolution
open scoped NNReal ENNReal
local instance firstGammaTestFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance firstGammaTestFields_sigma : MeasurableSpace StoppedFourier.CircleL2 := borel _
local instance firstGammaTestFields_borel : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (htarget : ∀ i,(b:ℝ)≤(Z i).target)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => FirstGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "R" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)

def value (p : Inputs) (t : ℝ) (z : FirstGammaAffine.Space n) : ℝ :=
  FirstGammaGaussianTest.test (W p) F Λ θ (fun i=>(Z i).target) t z

def derivative (p : Inputs) (t : ℝ) (z : FirstGammaAffine.Space n) : ℝ :=
  FirstGammaGaussianTest.testDerivative (W p) F Λ θ (fun i=>(Z i).target) t z

theorem value_apply (p : Inputs) (t : ℝ) (z : FirstGammaAffine.Space n) :
    value P Λ θ v b hvb Z htarget F p t z=backward (W p) F t (L t z)-backward (W p) F t (R z) := by
  change gaussianAverage ((W p).path t).val F (L t z+0)-
    gaussianAverage ((W p).path t).val F (R z+0)=_
  simp only [add_zero]
  rfl

include hF

theorem smoothTimeTest (hΛ : 0≤Λ) (p : Inputs) :
    LocalizedItoTest.SmoothTimeTest v b (value P Λ θ v b hvb Z htarget F p)
      (derivative P Λ θ v b hvb Z htarget F p) :=
  FirstGammaGaussianTest.smoothTimeTest (W p) v.2 hF hΛ θ (fun i=>(Z i).target)

include hF in
theorem value_joint_measurable : Measurable
    (fun p : (Inputs×ℝ)×FirstGammaAffine.Space n=>value P Λ θ v b hvb Z htarget F p.1.1 p.1.2 p.2) := by
  have hm:=ControlledGaussianComparisonFields.base_value_joint_measurable P Λ θ v b hvb Z htarget F hF
  have hL:=DampedAffineGaussian.continuous_linear Λ θ
    (FirstGammaAffine.baseCurrent n Λ θ (fun i=>(Z i).target)) (FirstGammaAffine.dynamic n)
  have hc : Continuous (fun p : (Inputs×ℝ)×FirstGammaAffine.Space n=>L p.1.2 p.2) :=
    (hL.comp continuous_fst.snd).clm_apply continuous_snd
  have hcm : Measurable (fun p : (Inputs×ℝ)×FirstGammaAffine.Space n=>L p.1.2 p.2) :=
    (isBoundedBilinearMap_apply (𝕜:=ℝ)).continuous.measurable.comp
      ((hL.measurable.comp measurable_fst.snd).prodMk measurable_snd)
  have hl:=hm.comp (measurable_fst.prodMk hcm)
  have hr:=hm.comp (measurable_fst.prodMk ((R).measurable.comp measurable_snd))
  simp_rw [value_apply]
  exact hl.sub hr

include hF in
theorem uniformSmooth (hΛ : 0≤Λ) : UniformBoundedSmooth
    (fun p : Inputs×ℝ=>value P Λ θ v b hvb Z htarget F p.1 p.2) := by
  have hb := (UniformBoundedSmooth.fixed (P:=Inputs×ℝ) hF).average
    (fun p : Inputs×ℝ=>ProbabilityTheory.multivariateGaussian (0:WordRecursion.State n) ((W p.1).path p.2).val)
    (fun _=>inferInstance)
  let K:=‖FirstGammaAffine.baseCurrent n Λ θ (fun i=>(Z i).target)‖+|θ| * ‖FirstGammaAffine.dynamic n‖
  have hK : 0≤K:=by positivity
  have hc:=UniformAffineSmooth.comp_affine hb (fun p : Inputs×ℝ=>L p.2) (fun _=>0) hK
    (fun p=>DampedAffineGaussian.linear_bound hΛ θ _ _ p.2)
  have hr:=UniformAffineSmooth.comp_affine hb (fun _ : Inputs×ℝ=>R) (fun _=>0) (norm_nonneg R)
    (fun _=>le_rfl)
  have hh:=hc.sub hr
  exact hh

set_option backward.isDefEq.respectTransparency true in
include hF in
theorem gradient_joint_measurable (hΛ : 0≤Λ) : Measurable
    (fun p : Inputs×(ℝ×FirstGammaAffine.Space n)=>fderiv ℝ
      (value P Λ θ v b hvb Z htarget F p.1 p.2.1) p.2.2) := by
  have hd : ∀ p : Inputs×ℝ,Differentiable ℝ (value P Λ θ v b hvb Z htarget F p.1 p.2) :=
    fun p=>(uniformSmooth P Λ θ v b hvb Z htarget F hF hΛ).smooth p |>.differentiable (by simp)
  have hm:=MeasurableDerivatives.fderiv_measurable (n:=(n+n)+(n+n)) (G:=ℝ)
    (F:=fun p : Inputs×ℝ=>value P Λ θ v b hvb Z htarget F p.1 p.2)
    (value_joint_measurable P Λ θ v b hvb Z htarget F hF) hd
  have hmap : Measurable (fun p : Inputs×(ℝ×FirstGammaAffine.Space n)=>((p.1,p.2.1),p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hh:=hm.comp hmap
  exact hh

variable (hΛ : 0≤Λ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
include hF hΛ hsmall in
theorem value_parameter_continuous (t : ℝ) : Continuous
    (fun p : Inputs×FirstGammaAffine.Space n=>value P Λ θ v b hvb Z htarget F p.1 t p.2) := by
  have hc:=ControlledReferenceCovariance.backward_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t
  have hl:=hc.comp (continuous_fst.prodMk ((L t).continuous.comp continuous_snd))
  have hr:=hc.comp (continuous_fst.prodMk ((R).continuous.comp continuous_snd))
  simp_rw [value_apply]
  exact hl.sub hr

end SHE.FirstGammaTestFields
