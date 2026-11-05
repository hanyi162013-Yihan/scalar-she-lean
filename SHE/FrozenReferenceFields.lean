module

public import SHE.ControlledResidualField
public import SHE.PredictablePastParameter
public import SHE.NativeObservationProcess

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.FrozenReferenceFields
open Set MeasureTheory ControlledProfile StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The frozen residual field uses the actual past pair after v.
Before v its input is fixed, so it is legitimately predictable for the
original filtration. Post-v integrals are independent of that choice. -/
def field (P : CanonicalCovariance.ProfileParameters) (Λ κ θ : ℝ) (hκ : κ<P.lower)
    (v : ℝ≥0) (data : Ω → Inputs) (p : ℝ≥0 × Ω) :
    FiniteHaar.EllipticField (P.lower-κ) (P.upper-κ) :=
  ControlledResidualField.field P Λ κ hκ
    ((PredictablePastParameter.held v data (0,0) p,θ),((p.1:ℝ)-(v:ℝ)))

theorem field_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : CanonicalCovariance.ProfileParameters) (Λ κ θ : ℝ) (hκ : κ<P.lower)
    (v : ℝ≥0) (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data) :
    StronglyMeasurable[𝓕.predictable] (field P Λ κ θ hκ v data) := by
  have hd := PredictablePastParameter.held_measurable 𝓕 v data hdata (0,0)
  have ht := (PredictableClock.real_time_measurable 𝓕).sub_const (v:ℝ)
  have hmap : @Measurable (ℝ≥0 × Ω) ControlledResidualField.Parameters 𝓕.predictable _
      (fun p => ((PredictablePastParameter.held v data (0,0) p,θ),((p.1:ℝ)-(v:ℝ)))) :=
    (hd.prodMk measurable_const).prodMk ht
  exact ((ControlledResidualField.field_measurable P Λ κ hκ).comp hmap).stronglyMeasurable

/-- Exact physical coefficient of the actual Haar field, for every
post-v sample/time and almost every spatial point. -/
theorem field_ae (P : CanonicalCovariance.ProfileParameters) (Λ κ θ : ℝ) (hκ : κ<P.lower)
    (v : ℝ≥0) (data : Ω → Inputs) (p : ℝ≥0 × Ω) (hp : v<p.1) :
    CircleNormalization.push (field P Λ κ θ hκ v data p).val =ᵐ[AddCircle.haarAddCircle]
      fun x => ((ControlledProfile.profile P Λ (data p.2).1 (data p.2).2
        (θ,((p.1:ℝ)-(v:ℝ),x))-κ : ℝ):ℂ) := by
  unfold field
  rw [ControlledResidualField.push_field,PredictablePastParameter.held_eq data (0,0) hp]
  exact ControlledResidualField.native_ae P Λ κ hκ _

end SHE.FrozenReferenceFields
