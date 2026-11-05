module

public import SHE.InverseClockNaturality
public import SHE.PastItoAlgebra
public import SHE.TwoChannelRawDriver

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω C D E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [NormedAddCommGroup D] [InnerProductSpace ℝ D] [MeasurableSpace D] [BorelSpace D]
variable [SecondCountableTopology D]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0 < c) (h : ℝ≥0)
local instance inverseClockChannels_local0 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

/-- A constant cylindrical isometry is exactly its bounded linear action
on predictable L2. -/
theorem constant_rotation_compLpL (L : C →ₗᵢ[ℝ] D)
    (hL : @Measurable ((ℝ≥0 × Ω) × C) D
      (𝓕.predictable.prod ‹MeasurableSpace C›) ‹MeasurableSpace D› (fun p => L p.2))
    (v : Process (E := C) 𝓕 μ h) :
    PredictableItoRotation.processIsometry 𝓕 μ h (fun _ => L) hL v =
      (L.toContinuousLinearMap.compLpL 2
        ((energyMeasure μ h).trim (predictable_le_product 𝓕))) v := by
  apply PastItoAlgebra.eq_of_ambient_ae
  exact (PredictableItoRotation.processIsometry_ae 𝓕 μ h (fun _ => L) hL v).trans
    (ae_eq_of_ae_eq_trim (L.toContinuousLinearMap.coeFn_compLpL v)).symm

/-- Restricting a whole cylindrical integral to a fixed isometric channel
commutes with inverting the Brownian clock, for the SAME integral map. -/
theorem inverse_constant_rotation
    (J : StandardTerminalIto (C := D) (E := E)
      (filtration 𝓕 (clock c hc)) μ (c*h))
    (L : C →ₗᵢ[ℝ] D)
    (hLU : @Measurable ((ℝ≥0 × Ω) × C) D
      (𝓕.predictable.prod ‹MeasurableSpace C›) ‹MeasurableSpace D› (fun p => L p.2))
    (hLN : @Measurable ((ℝ≥0 × Ω) × C) D
      ((filtration 𝓕 (clock c hc)).predictable.prod ‹MeasurableSpace C›)
      ‹MeasurableSpace D› (fun p => L p.2)) :
    inverseIntegral 𝓕 μ c hc h
      (PredictableItoRotation.integral (filtration 𝓕 (clock c hc)) μ (c*h)
        (fun _ => L) hLN J) =
    PredictableItoRotation.integral 𝓕 μ h (fun _ => L) hLU
      (inverseIntegral 𝓕 μ c hc h J) := by
  apply terminalIto_eq_of_integral_eq
  apply DFunLike.ext
  intro v
  change J.integral (PredictableItoRotation.processIsometry
    (filtration 𝓕 (clock c hc)) μ (c*h) (fun _ => L) hLN
      ((processEquivalence 𝓕 μ c hc h).symm v)) =
    J.integral ((processEquivalence 𝓕 μ c hc h).symm
      (PredictableItoRotation.processIsometry 𝓕 μ h (fun _ => L) hLU v))
  rw [constant_rotation_compLpL, constant_rotation_compLpL]
  exact congrArg J.integral
    (processEquivalence_symm_compLpL 𝓕 μ c hc h L.toContinuousLinearMap v)

local instance inverseClockChannels_local1 : MeasurableSpace (Both C) := borel _
local instance inverseClockChannels_local2 : BorelSpace (Both C) := ⟨rfl⟩
variable [SecondCountableTopology C]

/-- Exact channel identity used to attach inverse-clock Hilbert
naturality to the joint raw-driver common-law construction. -/
theorem inverse_leftIntegral
    (J : StandardTerminalIto (C := Both C) (E := E)
      (filtration 𝓕 (clock c hc)) μ (c*h)) :
    inverseIntegral 𝓕 μ c hc h
      (leftIntegral (filtration 𝓕 (clock c hc)) μ (c*h) J) =
    leftIntegral 𝓕 μ h (inverseIntegral 𝓕 μ c hc h J) :=
  inverse_constant_rotation 𝓕 μ c hc h J left
    (left_measurable 𝓕) (left_measurable (filtration 𝓕 (clock c hc)))

theorem inverse_rightIntegral
    (J : StandardTerminalIto (C := Both C) (E := E)
      (filtration 𝓕 (clock c hc)) μ (c*h)) :
    inverseIntegral 𝓕 μ c hc h
      (rightIntegral (filtration 𝓕 (clock c hc)) μ (c*h) J) =
    rightIntegral 𝓕 μ h (inverseIntegral 𝓕 μ c hc h J) :=
  inverse_constant_rotation 𝓕 μ c hc h J right
    (right_measurable 𝓕) (right_measurable (filtration 𝓕 (clock c hc)))

end SHE.PredictableTimeDilation
