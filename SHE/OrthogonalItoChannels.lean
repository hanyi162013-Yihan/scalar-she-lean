module

public import SHE.PredictableItoRotation
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.OrthogonalItoChannels
open MeasureTheory PredictableL2 PredictableItoRotation
open scoped NNReal ENNReal

variable {C E Ω : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Both (C : Type*) [NormedAddCommGroup C] := WithLp 2 (C × C)
local instance : MeasurableSpace (Both C) := borel _
local instance : BorelSpace (Both C) := ⟨rfl⟩

def left : C →ₗᵢ[ℝ] Both C where
  toFun x := WithLp.toLp 2 (x,0)
  map_add' x y := by apply WithLp.ofLp_injective; ext <;> simp
  map_smul' r x := by apply WithLp.ofLp_injective; ext <;> simp
  norm_map' x := WithLp.norm_toLp_fst 2 C C x

def right : C →ₗᵢ[ℝ] Both C where
  toFun x := WithLp.toLp 2 (0,x)
  map_add' x y := by apply WithLp.ofLp_injective; ext <;> simp
  map_smul' r x := by apply WithLp.ofLp_injective; ext <;> simp
  norm_map' x := WithLp.norm_toLp_snd 2 C C x

theorem inner_left_right (x y : C) : inner ℝ (left x) (right y)=0 := by
  simp [left,right,WithLp.prod_inner_apply]

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)

theorem left_measurable :
    @Measurable ((ℝ≥0 × Ω) × C) (Both C) (𝓕.predictable.prod ‹MeasurableSpace C›) _
      (fun p => left p.2) := left.continuous.measurable.comp measurable_snd
theorem right_measurable :
    @Measurable ((ℝ≥0 × Ω) × C) (Both C) (𝓕.predictable.prod ‹MeasurableSpace C›) _
      (fun p => right p.2) := right.continuous.measurable.comp measurable_snd

def leftIntegral (I : StandardTerminalIto (C := Both C) (E := E) 𝓕 μ h) :
    StandardTerminalIto (C := C) (E := E) 𝓕 μ h :=
  PredictableItoRotation.integral (A := C) (C := Both C) (E := E) 𝓕 μ h
    (fun (_ : ℝ≥0 × Ω) => left (C := C)) (left_measurable (C := C) 𝓕) I
def rightIntegral (I : StandardTerminalIto (C := Both C) (E := E) 𝓕 μ h) :
    StandardTerminalIto (C := C) (E := E) 𝓕 μ h :=
  PredictableItoRotation.integral (A := C) (C := Both C) (E := E) 𝓕 μ h
    (fun (_ : ℝ≥0 × Ω) => right (C := C)) (right_measurable (C := C) 𝓕) I

theorem left_bdg16 [SFinite μ] (I : StandardTerminalIto (C := Both C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) :
    StandardTerminalBDG16 (leftIntegral 𝓕 μ h I) B :=
  PredictableItoRotation.bdg16 (A := C) (C := Both C) (E := E) 𝓕 μ h
    (fun (_ : ℝ≥0 × Ω) => left (C := C)) (left_measurable (C := C) 𝓕) I B hBDG
theorem right_bdg16 [SFinite μ] (I : StandardTerminalIto (C := Both C) (E := E) 𝓕 μ h)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) :
    StandardTerminalBDG16 (rightIntegral 𝓕 μ h I) B :=
  PredictableItoRotation.bdg16 (A := C) (C := Both C) (E := E) 𝓕 μ h
    (fun (_ : ℝ≥0 × Ω) => right (C := C)) (right_measurable (C := C) 𝓕) I B hBDG

/-- Both noise channels come from one integral, and their ranges are
orthogonal in the actual terminal L² space. No independence surrogate
or separately supplied channel covariance is used. -/
theorem integral_inner_zero (I : StandardTerminalIto (C := Both C) (E := E) 𝓕 μ h)
    (v w : Process (E := C) 𝓕 μ h) :
    inner ℝ ((leftIntegral 𝓕 μ h I).integral v) ((rightIntegral 𝓕 μ h I).integral w)=0 := by
  let l := processIsometry 𝓕 μ h (fun _ => left (C := C)) (left_measurable 𝓕)
  let r := processIsometry 𝓕 μ h (fun _ => right (C := C)) (right_measurable 𝓕)
  change inner ℝ (I.integral (l v)) (I.integral (r w))=0
  rw [I.integral.inner_map_map,L2.inner_def]
  apply integral_eq_zero_of_ae
  have hm : @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable _ (fun p => inner ℝ (l v p) (r w p)) :=
    continuous_inner.measurable.comp
      ((Lp.stronglyMeasurable (l v)).measurable.prodMk (Lp.stronglyMeasurable (r w)).measurable)
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕) hm measurable_const
  filter_upwards [processIsometry_ae 𝓕 μ h (fun _ => left (C := C)) (left_measurable 𝓕) v,
    processIsometry_ae 𝓕 μ h (fun _ => right (C := C)) (right_measurable 𝓕) w] with p hp hq
  change inner ℝ (l v p) (r w p)=0
  rw [hp,hq,inner_left_right]

end SHE.OrthogonalItoChannels
