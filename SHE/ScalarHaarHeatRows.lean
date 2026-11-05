module
public import SHE.ScalarHaarRotation
public import SHE.NativeObservationCovariance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.ScalarHaarHeatRows
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor StoppedFourier
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

def test (τ : ℝ) (x : HeatCircle) : RealL2 :=
  realPart (CircleNormalization.push.symm (circleHeat τ x))

theorem embed_test {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) :
    realEmbed (test τ x) = CircleNormalization.push.symm (circleHeat τ x) :=
  NativeHeatObservation.realEmbed_realPart_of_real _
    (CircleNormalization.push_symm_ae_property _ (fun z => z.im=0) (circleHeat_real_ae hτ x))

/-- The literal original-target native Haar pair is the physical
one-noise heat row after the SAME solution-dependent orthogonal map. -/
theorem analysis (D : SmoothApproximation.ScalarData) (u : RealL2)
    {T r : ℝ} (hr : r < T) (x : HeatCircle) :
    ScalarHaarRotation.rotation D u
      (WithLp.toLp 2
        (NativeObservationCovariance.row (sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D))
          (AdditiveHaarForcing.constantField ((ScalarHaarRotation.amplitude D)^2)
            (sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D))) T r x,
        NativeObservationCovariance.row D.ell_pos (ScalarHaarRotation.residual D u) T r x)) =
    WithLp.toLp 2
      (ScalarSplittingInputs.originalInput haarAddCircle (ScalarHaarRotation.scalar D u)
        (ScalarHaarRotation.scalar_measurable D u) D.upper (ScalarHaarRotation.scalar_bound D u)
        (test (T-r) x),0) := by
  have he := ScalarHaarSplitting.analysis D.ell_pos (ScalarHaarRotation.residual D u)
    (ScalarHaarRotation.scalar D u) (ScalarHaarRotation.scalar_measurable D u)
    (ScalarHaarRotation.amplitude D) D.upper (ScalarHaarRotation.amplitude_pos D)
    (ScalarHaarRotation.scalar_gap D u) (ScalarHaarRotation.scalar_bound D u)
    (ScalarHaarRotation.residual_variance D u) (test (T-r) x)
  rw [embed_test (sub_pos.mpr hr) x] at he
  exact he
end SHE.ScalarHaarHeatRows
