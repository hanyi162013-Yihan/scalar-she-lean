module

public import SHE.NativeRootKernel
public import SHE.HaarMeasurable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeHaarKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped BigOperators ENNReal
local instance nativeHaarKernel_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeHaarKernel_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeHaarKernel_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeHaarKernel_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeHaarKernel_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeHaarKernel_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeHaarKernel_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeHaarKernel_inputMeasurable : MeasurableSpace FiniteHaar.HaarInput := borel FiniteHaar.HaarInput
local instance nativeHaarKernel_inputBorel : BorelSpace FiniteHaar.HaarInput := ⟨rfl⟩

def inputBasis : HilbertBasis FiniteHaar.HaarNode ℂ FiniteHaar.HaarInput :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem inputBasis_apply (q : FiniteHaar.HaarNode) : inputBasis q=lp.single 2 q 1 := by
  rw [← inputBasis.repr_symm_single q]
  rfl

/-- The literal common-Haar noise factor in native spatial coordinates. -/
def factor (m U : ℝ) (hm : 0 < m) (c : FiniteHaar.EllipticField m U) :
    FiniteHaar.HaarInput →L[ℂ] CircleL2 :=
  CircleNormalization.push.toLinearIsometry.toContinuousLinearMap.comp (FiniteHaar.fieldFactor m U hm c)

theorem factor_basis (m U : ℝ) (hm : 0 < m) (c : FiniteHaar.EllipticField m U)
    (q : FiniteHaar.HaarNode) : factor m U hm c (inputBasis q)=
      CircleNormalization.push (FiniteHaar.globalHaarColumn q c.1) := by
  rw [inputBasis_apply]
  change CircleNormalization.push (FiniteHaar.factor c.1 m U hm c.2.1 c.2.2 (lp.single 2 q 1))=_
  rw [FiniteHaar.factor_single]

theorem factor_norm_sq_le (m U : ℝ) (hm : 0 < m) (c : FiniteHaar.EllipticField m U) :
    ‖factor m U hm c‖^2 ≤ U := by
  have hU := FiniteHaar.elliptic_upper_nonneg c.1 m U hm c.2.2
  have hn : ‖factor m U hm c‖ ≤ Real.sqrt U := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg U)
    intro x
    change ‖CircleNormalization.push (FiniteHaar.fieldFactor m U hm c x)‖≤_
    rw [LinearIsometryEquiv.norm_map]
    exact FiniteHaar.fieldFactor_bound m U hm c x
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hU)

theorem factor_column_measurable {Ω : Type*} [MeasurableSpace Ω]
    (m U : ℝ) (hm : 0 < m) (c : Ω → FiniteHaar.EllipticField m U)
    (hc : Measurable c) (q : FiniteHaar.HaarNode) :
    Measurable (fun ω => factor m U hm (c ω) (inputBasis q)) := by
  exact CircleNormalization.push.continuous.measurable.comp
    ((FiniteHaar.continuous_fieldFactor_action m U hm (inputBasis q)).measurable.comp hc)

/-- Actual heated negative-output common-Haar columns, with a random
coefficient and random spatial kernel driven by the same probability
space. The coefficient's noise-factor applicability is fully discharged. -/
theorem expected_actual_Haar_trace
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1) (ha : ∀ i, Measurable (a i))
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B K Λ ρ m U : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (hK : 0 ≤ K) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hsharp : ∀ y x, ProfileL2.normTwo μ (fun ω => ‖F (ω,(y,x))‖) ≤
      K*NativeRootPartition.total t a (y,x))
    (hm : 0 < m) (hU : 0 ≤ U) (c : Ω → FiniteHaar.EllipticField m U) (hc : Measurable c) :
    Integrable (fun ω => ∑' q : FiniteHaar.HaarNode,
      ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω
        (CircleNormalization.push (FiniteHaar.globalHaarColumn q (c ω).1)))‖^2) μ ∧
      (∫ ω, ∑' q : FiniteHaar.HaarNode,
        ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω
          (CircleNormalization.push (FiniteHaar.globalHaarColumn q (c ω).1)))‖^2 ∂μ) ≤
        U*((Fintype.card I:ℝ)*∑ i, GaussianNegativePacket.constant ρ*
          (NativeHeatSpan.clock (t i))^(ρ-1/2)*K^2) ∧
      (∫ ω, ∑' q : FiniteHaar.HaarNode,
        ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω
          (CircleNormalization.push (FiniteHaar.globalHaarColumn q (c ω).1)))‖^2 ∂μ) ≤
        U*((Fintype.card I:ℝ)*∑ i, GaussianNegativePacket.traceConstant*Λ^(-ρ)*
          (NativeHeatSpan.clock (t i))^(-(1/2:ℝ))*K^2) := by
  have h := NativeRootPartition.expected_negative_right_trace μ t a ht ht1 ha hF hB hb hK hΛ hρ hρhalf
    hsharp (fun ω => factor m U hm (c ω)) inputBasis hU (fun ω => factor_norm_sq_le m U hm (c ω))
    (factor_column_measurable m U hm c hc)
  simpa only [ContinuousLinearMap.comp_apply,factor_basis] using h

end SHE.NativeHaarKernel
