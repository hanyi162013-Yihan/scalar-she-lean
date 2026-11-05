module
public import SHE.ScalarHeatSixFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.ScalarHeatSixNorms
open MeasureTheory StoppedFourier SmoothCylinders ScalarGaussianSemigroup
local instance scalarHeatSixNorms_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X : Type*} [MeasurableSpace X]
variable {a : ℝ→ℝ} (ha:BoundedSmooth a) {A β:ℝ} (hA:0≤A) (hβ:0≤β) (hβ1:β≤1)
variable (hh:∀x y,|a x-a y|≤A*|x-y|^β) (j:ℕ)
variable {σ0 σ1 z0 z1 m0 m1:X×HeatCircle→ℝ}
variable (hσ0:Measurable σ0) (hσ1:Measurable σ1) (hz0:Measurable z0) (hz1:Measurable z1)
variable (hm0:Measurable m0) (hm1:Measurable m1)

include ha hA hβ hβ1 hh hσ0 hσ1 hz0 hz1 hm0 hm1

/-- Literal spatial norm of the corrected-current root slot. -/
theorem current (p:X):
    let G:=ScalarHeatSixFields.fields a j σ0 σ1 z0 z1 m0 m1
    ‖NativeRandomRows.nativeRow (G 0) p-NativeRandomRows.nativeRow (G 1) p‖^2=
      ∫x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z0 (p,x))-
        deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 (p,x))|^2 ∂AddCircle.haarAddCircle:=by
  intro G
  change ‖ScalarHeatSingleMultiplier.multiplier a j σ0 z0 p-
    ScalarHeatSingleMultiplier.multiplier a j σ0 z1 p‖^2=_
  exact ScalarHeatPairedMultipliers.difference_norm ha hA hβ hβ1 hh j hσ0 hσ0 hz0 hz1 p

/-- Literal spatial norm of the current variance-change slot. -/
theorem current_variance (p:X):
    let G:=ScalarHeatSixFields.fields a j σ0 σ1 z0 z1 m0 m1
    ‖NativeRandomRows.nativeRow (G 1) p-NativeRandomRows.nativeRow (G 2) p‖^2=
      ∫x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 (p,x))-
        deriv (heat (σ1 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 (p,x))|^2 ∂AddCircle.haarAddCircle:=by
  intro G
  change ‖ScalarHeatSingleMultiplier.multiplier a j σ0 z1 p-
    ScalarHeatSingleMultiplier.multiplier a j σ1 z1 p‖^2=_
  exact ScalarHeatPairedMultipliers.difference_norm ha hA hβ hβ1 hh j hσ0 hσ1 hz1 hz1 p

/-- Literal spatial norm of the compatible frozen-root slot. -/
theorem reference (p:X):
    let G:=ScalarHeatSixFields.fields a j σ0 σ1 z0 z1 m0 m1
    ‖NativeRandomRows.nativeRow (G 3) p-NativeRandomRows.nativeRow (G 4) p‖^2=
      ∫x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m0 (p,x))-
        deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m1 (p,x))|^2 ∂AddCircle.haarAddCircle:=by
  intro G
  change ‖ScalarHeatSingleMultiplier.multiplier a j σ0 m0 p-
    ScalarHeatSingleMultiplier.multiplier a j σ0 m1 p‖^2=_
  exact ScalarHeatPairedMultipliers.difference_norm ha hA hβ hβ1 hh j hσ0 hσ0 hm0 hm1 p

/-- Literal spatial norm of the frozen-reference variance-change slot. -/
theorem reference_variance (p:X):
    let G:=ScalarHeatSixFields.fields a j σ0 σ1 z0 z1 m0 m1
    ‖NativeRandomRows.nativeRow (G 4) p-NativeRandomRows.nativeRow (G 5) p‖^2=
      ∫x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m1 (p,x))-
        deriv (heat (σ1 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m1 (p,x))|^2 ∂AddCircle.haarAddCircle:=by
  intro G
  change ‖ScalarHeatSingleMultiplier.multiplier a j σ0 m1 p-
    ScalarHeatSingleMultiplier.multiplier a j σ1 m1 p‖^2=_
  exact ScalarHeatPairedMultipliers.difference_norm ha hA hβ hβ1 hh j hσ0 hσ1 hm1 hm1 p
end SHE.ScalarHeatSixNorms
