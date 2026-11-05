module

public import SHE.ScalarApproximationDiscrepancy
public import SHE.MixedNativeCoefficientField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeApproximationInput
open MeasureTheory AddCircle StoppedFourier SmoothApproximation ScalarData ScalarApproximationDiscrepancy
open scoped ENNReal
local instance nativeApproximationInput_nativePositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeApproximationInput_unitPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local instance nativeApproximationInput_realSigma : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance nativeApproximationInput_realBorel : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
local instance nativeApproximationInput_unitSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance nativeApproximationInput_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeApproximationInput_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance nativeApproximationInput_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeApproximationInput_finiteExponent : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
local instance nativeApproximationInput_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

variable (D : ScalarData) (Λ ρ : ℝ) (hΛ : 1≤Λ) (hρ : 0≤ρ)

def original (U V : DyadicApproximation.RealL2) : CircleL2 :=
  OneInputOperator.besselHalf Λ ρ hΛ hρ (CircleNormalization.push (roughField D U-roughField D V))

def approximant (j : ℕ) (U V : DyadicApproximation.RealL2) : CircleL2 :=
  OneInputOperator.besselHalf Λ ρ hΛ hρ (CircleNormalization.push (smoothField D j U-smoothField D j V))

theorem difference_eq (j : ℕ) (U V : DyadicApproximation.RealL2) :
    original D Λ ρ hΛ hρ U V-approximant D Λ ρ hΛ hρ j U V=
      OneInputOperator.besselHalf Λ ρ hΛ hρ (CircleNormalization.push (differenceError D j U V)) := by
  simp only [original,approximant,differenceError,map_sub]

/-- This is the actual native massive negative-input field used in the
energy bridge, rather than a positive kernel envelope. Its smoothing
error is bounded uniformly over all dependent current states. -/
theorem difference_bound (j : ℕ) (U V : DyadicApproximation.RealL2) :
    ‖original D Λ ρ hΛ hρ U V-approximant D Λ ρ hΛ hρ j U V‖≤SmoothReferenceLimit.error D j := by
  rw [difference_eq]
  exact ((OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _).trans_eq
    (CircleNormalization.push.norm_map _)).trans (difference_field_error D j U V)

theorem norm_comparison (j : ℕ) (U V : DyadicApproximation.RealL2) :
    |‖original D Λ ρ hΛ hρ U V‖-‖approximant D Λ ρ hΛ hρ j U V‖|≤SmoothReferenceLimit.error D j :=
  (abs_norm_sub_norm_le _ _).trans (difference_bound D Λ ρ hΛ hρ j U V)

theorem approximant_measurable {X : Type*} [MeasurableSpace X] (j : ℕ)
    (U V : X→DyadicApproximation.RealL2) (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun x=>approximant D Λ ρ hΛ hρ j (U x) (V x)) :=
  (OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp
    (CircleNormalization.push.continuous.measurable.comp
      (((smoothField_measurable D j).comp hU).sub ((smoothField_measurable D j).comp hV)))

theorem original_measurable {X : Type*} [MeasurableSpace X]
    (U V : X→DyadicApproximation.RealL2) (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun x=>original D Λ ρ hΛ hρ (U x) (V x)) :=
  (OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp
    (CircleNormalization.push.continuous.measurable.comp
      (((roughField_measurable D).comp hU).sub ((roughField_measurable D).comp hV)))

theorem error_energy {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (j : ℕ) (U V : X→DyadicApproximation.RealL2) (hU : Measurable U) (hV : Measurable V) :
    let e:=fun x=>original D Λ ρ hΛ hρ (U x) (V x)-approximant D Λ ρ hΛ hρ j (U x) (V x)
    Integrable (fun x=>‖e x‖^2) ν ∧
      (∫x,‖e x‖^2 ∂ν)≤SmoothReferenceLimit.error D j^2*(ν Set.univ).toReal := by
  intro e
  have hm:Measurable (fun x=>‖e x‖^2):=
    ((original_measurable D Λ ρ hΛ hρ U V hU hV).sub
      (approximant_measurable D Λ ρ hΛ hρ j U V hU hV)).norm.pow_const 2
  have hb(x:X):‖e x‖^2≤SmoothReferenceLimit.error D j^2:=
    pow_le_pow_left₀ (norm_nonneg _) (difference_bound D Λ ρ hΛ hρ j (U x) (V x)) 2
  have hi:Integrable (fun x=>‖e x‖^2) ν:=
    (integrable_const (SmoothReferenceLimit.error D j^2)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hb x))
  refine ⟨hi,?_⟩
  calc
    _≤∫_x:X,SmoothReferenceLimit.error D j^2 ∂ν:=integral_mono hi (integrable_const _) hb
    _=SmoothReferenceLimit.error D j^2*(ν Set.univ).toReal:=by
      rw [integral_const]
      change (ν Set.univ).toReal*_=_
      ring

end SHE.NativeApproximationInput
