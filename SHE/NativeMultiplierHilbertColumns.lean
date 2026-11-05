module

public import SHE.NativeMultiplierColumnFields
public import SHE.NativeOutputTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SHE.NativeMultiplierHilbertColumns
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation NativeRandomKernel
open scoped NNReal ENNReal
local instance nativeMultiplierHilbertColumns_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeMultiplierHilbertColumns_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeMultiplierHilbertColumns_sigma : MeasurableSpace CircleL2:=borel _
local instance nativeMultiplierHilbertColumns_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeMultiplierHilbertColumns_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeMultiplierHilbertColumns_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeMultiplierHilbertColumns_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
abbrev Space := HilbertColumns.Space FiniteHaar.HaarNode CircleL2
local instance nativeMultiplierHilbertColumns_spaceSigma : MeasurableSpace Space:=borel _
local instance nativeMultiplierHilbertColumns_spaceBorel : BorelSpace Space:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

/-- The actual dependent multiplier, heat and countable Haar factor form
an honest Hilbert--Schmidt field. Its trace uses the spatial L2 norm of
that multiplier rather than a uniform pointwise replacement. -/
theorem trace {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hm : 0<m)
    {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ) (hb : ∀ p x,‖b (p,x)‖≤cap p)
    {t : P→ℝ} (htm : Measurable t) (ht : ∀ p,0<t p) (ht1 : ∀ p,t p≤1)
    (c : P→FiniteHaar.EllipticField m U) (p : P) :
    Summable (fun q=>‖NativeMultiplierColumnFields.column hΛ hρ b t hm c p q‖^2) ∧
      (∑' q,‖NativeMultiplierColumnFields.column hΛ hρ b t hm c p q‖^2)≤
        U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t p)^(ρ-1/2))*
          ‖NativeRandomRows.nativeRow b p‖^2 := by
  have hh:=NativeOutputTrace.output_right_trace hΛ hρ hρhalf (ht p) (ht1 p)
    (NativeRandomRows.nativeRow b p) (cap p) (NativeMultiplierColumnFields.row_bound hbm cap hb p)
    (NativeHaarKernel.factor m U hm (c p)) NativeHaarKernel.inputBasis
  have he (q : FiniteHaar.HaarNode) :
      NativeMultiplierColumnFields.column hΛ hρ b t hm c p q=
      ((OneInputOperator.besselHalf Λ ρ hΛ hρ).comp
        ((NativeMultiplierTrace.multiplier (NativeRandomRows.nativeRow b p) (cap p)
          (NativeMultiplierColumnFields.row_bound hbm cap hb p)).comp (circleHeatOperator (t p) (ht p).le))).comp
        (NativeHaarKernel.factor m U hm (c p)) (NativeHaarKernel.inputBasis q) := by
    simp only [ContinuousLinearMap.comp_apply,NativeHaarKernel.factor_basis]
    exact congrArg (OneInputOperator.besselHalf Λ ρ hΛ hρ)
      (NativeMultiplierColumnFields.operator_eq hbm cap hb htm ht p _)
  have hn : 0≤(1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t p)^(ρ-1/2):=
    mul_nonneg (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf]) (rpow_nonneg (ht p).le _)
  refine ⟨by simpa only [he] using hh.1,?_⟩
  calc
    _ ≤ ‖NativeHaarKernel.factor m U hm (c p)‖^2*
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(t p)^(ρ-1/2))*
        ‖NativeRandomRows.nativeRow b p‖^2 := by simpa only [he] using hh.2
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (NativeHaarKernel.factor_norm_sq_le m U hm (c p)) hn) (sq_nonneg _)

/-- Canonical actual infinite-column realization, with no supplied
Hilbert--Schmidt representative or stochastic integrability premise. -/
def columns {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hm : 0<m)
    {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ) (hb : ∀ p x,‖b (p,x)‖≤cap p)
    {t : P→ℝ} (htm : Measurable t) (ht : ∀ p,0<t p) (ht1 : ∀ p,t p≤1)
    (c : P→FiniteHaar.EllipticField m U) (p : P) : Space :=
  HilbertColumns.ofSummable (NativeMultiplierColumnFields.column hΛ hρ b t hm c p)
    (trace hΛ hρ hρhalf hm hbm cap hb htm ht ht1 c p).1

theorem columns_apply {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hm : 0<m)
    {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ) (hb : ∀ p x,‖b (p,x)‖≤cap p)
    {t : P→ℝ} (htm : Measurable t) (ht : ∀ p,0<t p) (ht1 : ∀ p,t p≤1)
    (c : P→FiniteHaar.EllipticField m U) (p : P) (q : FiniteHaar.HaarNode) :
    columns hΛ hρ hρhalf hm hbm cap hb htm ht ht1 c p q=
      NativeMultiplierColumnFields.column hΛ hρ b t hm c p q := rfl

/-- This is Borel for ANY parameter sigma algebra; in particular the
actual coefficient data can carry the original predictable sigma. -/
theorem columns_measurable {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hm : 0<m)
    {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ) (hb : ∀ p x,‖b (p,x)‖≤cap p)
    {t : P→ℝ} (htm : Measurable t) (ht : ∀ p,0<t p) (ht1 : ∀ p,t p≤1)
    (c : P→FiniteHaar.EllipticField m U) (hc : Measurable c) :
    Measurable (columns hΛ hρ hρhalf hm hbm cap hb htm ht ht1 c) := by
  apply HilbertColumns.measurable_of_columns
  intro q
  exact NativeMultiplierColumnFields.column_measurable hΛ hρ hm hbm cap hb htm ht c hc q

end SHE.NativeMultiplierHilbertColumns
