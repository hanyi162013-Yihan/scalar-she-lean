module
public import SHE.StandardTerminalGirsanov
public import SHE.NativeObservationNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.NativeGirsanovHilbertLift
open MeasureTheory PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels
open NativeObservationNaturality PredictableItoRotation
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (Q:Measure Ω) (H:ℝ≥0)
local notation "ν"=>((energyMeasure Q H).trim (predictable_le_product 𝓕))

/-- Ordinary column projection followed by a fixed channel embedding
is the same predictable L2 input as the two successive actions. -/
theorem channel_input (e:RealHaarInput→ₗᵢ[ℝ] Both RealHaarInput)
    (L:RealL2→L[ℝ] ℝ) (v:Process (E:=RealHaarIntegrand.Columns) 𝓕 Q H) :
    ((e.toContinuousLinearMap.comp (HilbertColumns.mapCLM L)).compLpL 2 ν) v =
      processIsometry 𝓕 Q H (fun _=>e)
        (e.continuous.measurable.comp measurable_snd)
        (((HilbertColumns.mapCLM L).compLpL 2 ν) v) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [ae_eq_of_ae_eq_trim
      ((e.toContinuousLinearMap.comp (HilbertColumns.mapCLM L)).coeFn_compLpL v),
    processIsometry_ae 𝓕 Q H (fun _=>e)
      (e.continuous.measurable.comp measurable_snd)
      (((HilbertColumns.mapCLM L).compLpL 2 ν) v),
    ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLpL v)] with p h1 h2 h3
  rw [h1,h2,h3]
  rfl

variable [IsProbabilityMeasure Q]

/-- Specialization of the accepted ordinary Hilbert realization to the
actual Haar channels. Both returned Hilbert maps commute with the SAME
changed scalar integral through the original native naturality interface. -/
theorem exists_natural (K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H)
    (hK:StandardHilbertItoLift K) :
    ∃I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H,
      StandardScalarNaturality I₀ (leftIntegral 𝓕 Q H K) ∧
      StandardScalarNaturality I₁ (rightIntegral 𝓕 Q H K) := by
  obtain ⟨I₀,I₁,h0,h1⟩:=hK HaarNode RealL2 (LinearIsometry.id)
  refine ⟨I₀,I₁,⟨?_⟩,⟨?_⟩⟩
  · intro L v
    have he:(L.compLpL 2 Q) (I₀.integral v)=K.integral
        (((left (C:=RealHaarInput)).toContinuousLinearMap.comp
          (HilbertColumns.mapCLM L)).compLpL 2 ν v):=h0 L v
    rw [channel_input 𝓕 Q H left L v] at he
    exact he
  · intro L v
    have he:(L.compLpL 2 Q) (I₁.integral v)=K.integral
        (((right (C:=RealHaarInput)).toContinuousLinearMap.comp
          (HilbertColumns.mapCLM L)).compLpL 2 ν v):=h1 L v
    rw [channel_input 𝓕 Q H right L v] at he
    exact he

end SHE.NativeGirsanovHilbertLift
