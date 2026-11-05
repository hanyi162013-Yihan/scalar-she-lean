module

public import SHE.SignedKernelColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.SignedKernelColumns
open MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped ENNReal
local instance rawKernelColumns_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance rawKernelColumns_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance rawKernelColumns_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance rawKernelColumns_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance rawKernelColumns_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance rawKernelColumns_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance rawKernelColumns_measurable : MeasurableSpace Space := borel Space
local instance rawKernelColumns_borel : BorelSpace Space := ⟨rfl⟩
variable {X : Type*} [MeasurableSpace X]

theorem native_heat_zero (v : CircleL2) : circleHeatOperator 0 (by norm_num) v=v := by
  apply (fourierBasis (T:=2*π)).repr.injective
  apply lp.ext
  funext i
  simp only [fourierBasis_repr,circleHeatOperator_fourierCoeff,neg_zero,zero_mul,exp_zero,
    Complex.ofReal_one,one_mul]

/-- The raw signed noise columns with no additional right heat. -/
def rawColumns (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (m U : ℝ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) : X → Space :=
  columns F Λ ρ (fun _ => 0) hΛ hρ (fun _ => le_rfl) m U hm c d

theorem rawColumns_apply (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (m U : ℝ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (x : X) (i : FiniteHaar.HaarNode) :
    rawColumns F Λ ρ hΛ hρ m U hm c d x i=
      OneInputOperator.besselHalf Λ ρ hΛ hρ
        (integralOperator F x (CircleNormalization.push
          (FiniteHaar.globalHaarColumn i (d x).1-FiniteHaar.globalHaarColumn i (c x).1))) := by
  simp only [rawColumns,columns_apply,column,zero_div,native_heat_zero]

theorem rawColumns_norm_sq (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (m U : ℝ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (x : X) :
    ‖rawColumns F Λ ρ hΛ hρ m U hm c d x‖^2=
      ∑' i : FiniteHaar.HaarNode,‖OneInputOperator.besselHalf Λ ρ hΛ hρ
        (integralOperator F x (CircleNormalization.push
          (FiniteHaar.globalHaarColumn i (d x).1-FiniteHaar.globalHaarColumn i (c x).1)))‖^2 := by
  rw [HilbertColumns.norm_sq]
  exact tsum_congr (fun i => congrArg (fun v : CircleL2 => ‖v‖^2) (rawColumns_apply F Λ ρ hΛ hρ m U hm c d x i))

/-- Actual raw Hilbert-valued noise rows are measurable under sectionwise
finite kernel bounds. This applies over a predictable sigma algebra when
the actual kernel and coefficient fields are predictable. -/
theorem rawColumns_measurable {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ x, ∃ B : ℝ, 0 ≤ B ∧ ∀ y z, ‖F (x,(y,z))‖ ≤ B)
    {Λ ρ m U : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (hc : Measurable c) (hd : Measurable d) :
    Measurable (rawColumns F Λ ρ hΛ hρ m U hm c d) :=
  columns_measurable hF hb (fun _ => 0) measurable_const hΛ hρ (fun _ => le_rfl) hm c d hc hd

end SHE.SignedKernelColumns
