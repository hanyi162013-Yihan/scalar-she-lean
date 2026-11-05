module
public import SHE.NativeHaarKernel
public import SHE.HilbertColumns
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeKernelEnergyHaar
open Set MeasureTheory AddCircle StoppedFourier FiniteHaar NativeRandomKernel
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : Fact (1≤(2:ENNReal)):=⟨by norm_num⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace NativeRandomKernel.KernelSpace:=borel _
local instance : BorelSpace NativeRandomKernel.KernelSpace:=⟨rfl⟩
local instance : SecondCountableTopology NativeRandomKernel.KernelSpace:=Lp.SecondCountableTopology
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω]

/-- Any proved complete-kernel negative energy passes to the ACTUAL
countable Haar columns, with the original arbitrarily dependent bounded
coefficient and a genuine right heat. No independence is required. -/
theorem heated_trace (μ:Measure Ω)[IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ}(hF:Measurable F)
    {B:ℝ}(hB:0≤B)(hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    {C:ℝ}(hi:Integrable (fun ω=>‖negativeKernel mass ρ hmass hρ F ω‖^2) μ)
    (he:(∫ω,‖negativeKernel mass ρ hmass hρ F ω‖^2 ∂μ)≤C)
    {ell M t:ℝ}(hell:0<ell)(hM:0≤M)(ht:0≤t)
    (c:Ω→EllipticField ell M)(hc:Measurable c):
    Integrable (fun ω=>∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ
      (integralOperator F ω (circleHeatOperator t ht
        (CircleNormalization.push (globalHaarColumn j (c ω).1))))‖^2) μ ∧
      (∫ω,∑'j:HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ
        (integralOperator F ω (circleHeatOperator t ht
          (CircleNormalization.push (globalHaarColumn j (c ω).1))))‖^2 ∂μ)≤M*C:=by
  let R:Ω→HaarInput→L[ℂ]CircleL2:=fun ω=>
    (circleHeatOperator t ht).comp (NativeHaarKernel.factor ell M hell (c ω))
  have hR:∀ω,‖R ω‖^2≤M:=by
    intro ω
    have hn:‖R ω‖≤‖NativeHaarKernel.factor ell M hell (c ω)‖:=by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      exact (circleHeatOperator_norm_le t ht _).trans
        ((NativeHaarKernel.factor ell M hell (c ω)).le_opNorm u)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
      (NativeHaarKernel.factor_norm_sq_le ell M hell (c ω))
  have hRm:∀j,Measurable (fun ω=>R ω (NativeHaarKernel.inputBasis j)):=by
    intro j
    exact (circleHeatOperator t ht).continuous.measurable.comp
      (NativeHaarKernel.factor_column_measurable ell M hell c hc j)
  have hh:=KernelOperator.expected_synthesis_right_trace_bound μ
    (negativeKernel mass ρ hmass hρ F) R
    (_root_.fourierBasis (T:=2*Real.pi)) (_root_.fourierBasis (T:=2*Real.pi))
    NativeHaarKernel.inputBasis (negativeKernel_measurable hmass hρ hF hB hb) hRm hM hR hi he
  have heq(ω:Ω)(j:HaarNode):
      ((KernelOperator.synthesis (negativeKernel mass ρ hmass hρ F ω)).comp (R ω))
        (NativeHaarKernel.inputBasis j)=
      OneInputOperator.besselHalf mass ρ hmass hρ
        (integralOperator F ω (circleHeatOperator t ht
          (CircleNormalization.push (globalHaarColumn j (c ω).1)))):=by
    rw [negative_synthesis_eq hmass hρ hF hB hb ω]
    simp only [ContinuousLinearMap.comp_apply,R,NativeHaarKernel.factor_basis]
  simpa only [heq] using hh
end SHE.NativeKernelEnergyHaar
