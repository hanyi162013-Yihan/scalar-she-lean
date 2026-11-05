module

public import SHEStochastic.MatrixUnboundedLocalFourierConvolution
public import SHEStochastic.FourierHeatRowAverage
public import SHEStochastic.StateNoiseCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixUnboundedNativeRowTransport
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar AddCircle
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local notation "ν₁" => AddCircle.haarAddCircle (T := (1 : ℝ))
local notation "ν₂" => AddCircle.haarAddCircle (T := 2*Real.pi)
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

private theorem weight_scale (a : ℂ →L[ℝ] ℝ) (m : ℤ) (x : HeatCircle) :
    NativeFourierHeatCoordinate.weight a m x =
      MatrixFourierCoordinates.weight a m (CircleNormalization.scale (2*Real.pi) 1 x) := by
  simp only [NativeFourierHeatCoordinate.weight,NativeScalarFourierWeight.value,
    MatrixFourierCoordinates.weight,ContinuousMap.coe_mk,one_mul]
  rw [CircleNormalization.fourier_scale]

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0×Ω → Physical (d := Fin n))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (a : ℂ →L[ℝ] ℝ) (m : ℤ)

/-- Rescaling the native Fourier coefficient row is exactly the original
unit-circle coefficient row. This is an equality of L2 noise fields. -/
theorem row (p : ℝ≥0×Ω) :
    FourierHeatRowAverage.row F
      (fun z => VectorNativeHaarBasis.equivalence (U z))
      ((VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable hU)
      hG hβ hβ1 a m p =
      VectorNativeHaarBasis.equivalence
        (StateNoiseCovariance.row ν₁ hβ hβ1.le hG
          (MatrixFourierCoordinates.weight a m) (U p)) := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  change HolderStateRows.row
    (fun z => VectorNativeHaarBasis.equivalence (U z))
    ((VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable hU)
    hG hβ hβ1.le (fun _ => NativeFourierHeatCoordinate.weight a m) p =
      VectorNativeHeatEndpoint.push
        (StateNoiseCovariance.row ν₁ hβ hβ1.le hG
          (MatrixFourierCoordinates.weight a m) (U p))
  apply Lp.ext
  have hp := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  filter_upwards [HolderStateRows.row_ae
      (fun z => VectorNativeHaarBasis.equivalence (U z))
      ((VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable hU)
      hG hβ hβ1.le (fun _ => NativeFourierHeatCoordinate.weight a m) p,
    VectorNativeHeatEndpoint.push_ae
      (StateNoiseCovariance.row ν₁ hβ hβ1.le hG
        (MatrixFourierCoordinates.weight a m) (U p)),
    VectorNativeHeatEndpoint.push_ae (U p),
    hp.ae (StateNoiseCovariance.row_ae ν₁ hβ hβ1.le hG
      (MatrixFourierCoordinates.weight a m) (U p))] with x hn hv hu hr
  change (VectorNativeHaarBasis.equivalence (U p)) x =
    U p (CircleNormalization.scale (2*Real.pi) 1 x) at hu
  rw [hn,hv,hr,hu,weight_scale]

end SHEStochastic.MatrixUnboundedNativeRowTransport
