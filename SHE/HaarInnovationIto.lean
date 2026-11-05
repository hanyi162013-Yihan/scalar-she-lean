module

public import SHE.PredictableItoRotation
public import SHE.HaarInnovationInverse
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
noncomputable section

namespace SHE.HaarInnovationIto
open MeasureTheory PredictableL2 FiniteHaar DyadicApproximation CircleHeat
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel RealL2
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance : BorelSpace RealHaarInput := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

def field (p : ℝ≥0 × Ω) : RealL2 →ₗᵢ[ℝ] RealHaarInput :=
  (fieldRealInnovation ell M hell (f p)).toLinearIsometry

theorem field_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) : @Measurable ((ℝ≥0 × Ω) × RealL2) RealHaarInput
    (𝓕.predictable.prod (borel RealL2)) (borel RealHaarInput)
      (fun p => field hell f p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  change Measurable (fun p : (ℝ≥0 × Ω) × RealL2 => fieldRealInnovation ell M hell (f p.1) p.2)
  have hp : Measurable (fun p : (ℝ≥0 × Ω) × RealL2 => (f p.1,p.2)) :=
    (hf.measurable.comp measurable_fst).prodMk measurable_snd
  have hh := (measurable_fieldRealInnovation_joint ell M hell).comp hp
  exact hh

def inverseField (p : ℝ≥0 × Ω) : RealHaarInput →ₗᵢ[ℝ] RealL2 :=
  (fieldRealInnovation ell M hell (f p)).symm.toLinearIsometry

theorem inverseField_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → EllipticField ell M)
    (hf : StronglyMeasurable[𝓕.predictable] f) : @Measurable ((ℝ≥0 × Ω) × RealHaarInput) RealL2
    (𝓕.predictable.prod (borel RealHaarInput)) (borel RealL2)
      (fun p => inverseField hell f p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  change Measurable (fun p : (ℝ≥0 × Ω) × RealHaarInput => (fieldRealInnovation ell M hell (f p.1)).symm p.2)
  have hp : Measurable (fun p : (ℝ≥0 × Ω) × RealHaarInput => (f p.1,p.2)) :=
    (hf.measurable.comp measurable_fst).prodMk measurable_snd
  have hh := (measurable_fieldRealInnovationInverse_joint ell M hell).comp hp
  exact hh

/-- The actual predictable physical-to-common-Haar innovation rotation,
lifted to the complete predictable L² space. -/
def rotation : Process (E := RealL2) 𝓕 μ h →ₗᵢ[ℝ] Process (E := RealHaarInput) 𝓕 μ h :=
  PredictableItoRotation.processIsometry 𝓕 μ h (field hell f) (field_measurable 𝓕 hell f hf)

def inverseRotation : Process (E := RealHaarInput) 𝓕 μ h →ₗᵢ[ℝ] Process (E := RealL2) 𝓕 μ h :=
  PredictableItoRotation.processIsometry 𝓕 μ h (inverseField hell f) (inverseField_measurable 𝓕 hell f hf)

theorem rotation_ae (v : Process (E := RealL2) 𝓕 μ h) :
    rotation 𝓕 μ h hell f hf v =ᵐ[energyMeasure μ h]
      (fun p => fieldRealInnovation ell M hell (f p) (v p)) :=
  PredictableItoRotation.processIsometry_ae 𝓕 μ h (field hell f) (field_measurable 𝓕 hell f hf) v

theorem inverseRotation_ae (v : Process (E := RealHaarInput) 𝓕 μ h) :
    inverseRotation 𝓕 μ h hell f hf v =ᵐ[energyMeasure μ h]
      (fun p => (fieldRealInnovation ell M hell (f p)).symm (v p)) :=
  PredictableItoRotation.processIsometry_ae 𝓕 μ h (inverseField hell f) (inverseField_measurable 𝓕 hell f hf) v

/-- Physical scalar Ito integration obtained by the actual predictable
Haar innovation. Its centering, adapted versions and exact isometry are
derived from ordinary common-coordinate Ito integration. -/
def physicalIntegral (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h) :
    StandardTerminalIto (C := RealL2) (E := ℝ) 𝓕 μ h :=
  PredictableItoRotation.integral 𝓕 μ h (field hell f) (field_measurable 𝓕 hell f hf) J

theorem physical_bdg16 [SFinite μ]
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B) :
    StandardTerminalBDG16 (physicalIntegral 𝓕 μ h hell f hf J) B :=
  PredictableItoRotation.bdg16 𝓕 μ h (field hell f) (field_measurable 𝓕 hell f hf) J B hBDG

end SHE.HaarInnovationIto
