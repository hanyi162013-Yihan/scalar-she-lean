module

public import SHE.ScalarHeatBandMultipliers
public import SHE.NativeHaarKernel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.ScalarHeatBandHaarTrace
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal
local instance scalarHeatBandHaarTrace_period : Fact (0<2*π):=⟨by positivity⟩
local instance scalarHeatBandHaarTrace_unitPeriod : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance scalarHeatBandHaarTrace_sigma : MeasurableSpace CircleL2:=borel _
local instance scalarHeatBandHaarTrace_borel : BorelSpace CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

/-- Genuine native negative-output trace for the SECOND complete-Gamma
term. The multiplier is the actual displaced Gaussian heat-band
gradient and every right column is the actual infinite Haar factor.
No independence or assumed trace bound occurs in the hypotheses. -/
theorem displaced_gradient_trace {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y) (p : P)
    (hσ : ∀ᵐ z∂haarAddCircle,lo≤σ (p,z))
    (hi : Integrable (fun z=>(y (p,z)-x (p,z))^2) haarAddCircle)
    {Λ ρ t m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (ht : 0<t) (ht1 : t≤1)
    (hm : 0<m) (c : FiniteHaar.EllipticField m U) :
    let b:=ScalarHeatBandMultipliers.multiplier a j σ x y p
    let B:=ScalarHeatBandMultipliers.cap H β j
    let hb:=ScalarHeatBandMultipliers.multiplier_bound ha hH hβ hβ1 hh j hσm hxm hym p
    let col:=fun q : FiniteHaar.HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ
      (NativeMultiplierTrace.multiplier b B hb (circleHeatOperator t ht.le
        (CircleNormalization.push (FiniteHaar.globalHaarColumn q c.1))))
    Summable (fun q=>‖col q‖^2) ∧
      (∑' q,‖col q‖^2)≤
        U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*
          ((2*H*ScalarHeatGradientDifference.constant β)*CompactMollifier.radius (j+1)^(β-1)*
            decay (CompactMollifier.radius (j+1)) lo ((3-β)/2))^2*
          min 1 ((∫ z,(y (p,z)-x (p,z))^2 ∂haarAddCircle)/CompactMollifier.radius (j+1)^2) := by
  intro b B hb col
  have htrace:=NativeOutputTrace.output_right_trace hΛ hρ hρhalf ht ht1 b B hb
    (NativeHaarKernel.factor m U hm c) NativeHaarKernel.inputBasis
  have hs : Summable (fun q=>‖col q‖^2):=by
    simpa only [ContinuousLinearMap.comp_apply,NativeHaarKernel.factor_basis,col] using htrace.1
  have hn:=ScalarHeatBandMultipliers.multiplier_energy ha hH hβ hβ1 hlo hh j hσm hxm hym p hσ hi
  have hC : 0≤(1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2):=
    mul_nonneg (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf]) (rpow_nonneg ht.le _)
  have hfactor:=NativeHaarKernel.factor_norm_sq_le m U hm c
  have hU : 0≤U:=FiniteHaar.elliptic_upper_nonneg c.1 m U hm c.2.2
  have he : (∑' q,‖col q‖^2)≤‖NativeHaarKernel.factor m U hm c‖^2*
      ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2))*‖b‖^2:=by
    simpa only [ContinuousLinearMap.comp_apply,NativeHaarKernel.factor_basis,col] using htrace.2
  refine ⟨hs,he.trans ?_⟩
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor hC) (sq_nonneg ‖b‖)).trans
  have hh':=mul_le_mul_of_nonneg_left hn (mul_nonneg hU hC)
  simpa only [mul_assoc] using hh'

end SHE.ScalarHeatBandHaarTrace
