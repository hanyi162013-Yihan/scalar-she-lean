module

public import SHE.FrozenReferenceFields
public import SHE.ControlledReferenceKernelEnergy
public import SHE.PastRelativeEnergy
public import SHE.PastItoInputs

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastReferenceBracket
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Literal signed frozen residual convolution columns on the original
physical time axis. Both interpolation endpoints use the same Haar
coordinates. The additive channel cancels. -/
def raw (P : CanonicalCovariance.ProfileParameters) (Λ κ θ η : ℝ) (hκ : κ<P.lower)
    (v b : ℝ≥0) (data : Ω → Inputs) (p : ℝ≥0 × Ω) : RealHaarIntegrand.Columns :=
  (Ioc v b ×ˢ (univ : Set Ω)).indicator (fun p =>
    NativeHeatObservation.kernel (P.lower-κ) (P.upper-κ) (sub_pos.mpr hκ)
      ((b:ℝ)-(p.1:ℝ),FrozenReferenceFields.field P Λ κ θ hκ v data p)-
    NativeHeatObservation.kernel (P.lower-κ) (P.upper-κ) (sub_pos.mpr hκ)
      ((b:ℝ)-(p.1:ℝ),FrozenReferenceFields.field P Λ κ η hκ v data p)) p

theorem raw_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : CanonicalCovariance.ProfileParameters) (Λ κ θ η : ℝ) (hκ : κ<P.lower)
    (v b : ℝ≥0) (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data) :
    StronglyMeasurable[𝓕.predictable] (raw P Λ κ θ η hκ v b data) := by
  have hk (a : ℝ) : StronglyMeasurable[𝓕.predictable] (fun p : ℝ≥0 × Ω =>
      NativeHeatObservation.kernel (P.lower-κ) (P.upper-κ) (sub_pos.mpr hκ)
        ((b:ℝ)-(p.1:ℝ),FrozenReferenceFields.field P Λ κ a hκ v data p)) := by
    have hm := (FrozenReferenceFields.field_predictable 𝓕 P Λ κ a hκ v data hdata).measurable
    exact ((NativeObservationProcess.kernel_measurable _ _ (sub_pos.mpr hκ)).comp
      ((measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).prodMk hm)).stronglyMeasurable
  exact ((hk θ).sub (hk η)).indicator
    (measurableSet_predictable_Ioc_prod v b MeasurableSet.univ)

theorem raw_norm_sq (P : CanonicalCovariance.ProfileParameters) (Λ κ θ η : ℝ) (hκ : κ<P.lower)
    (v b : ℝ≥0) (data : Ω → Inputs) (r : ℝ≥0) (ω : Ω) :
    ‖raw P Λ κ θ η hκ v b data (r,ω)‖^2 =
      (Ioc v b).indicator (fun s : ℝ≥0 => ControlledReferenceEnergy.kernelEnergy P Λ κ hκ
        (data ω).1 (data ω).2 θ η ((b:ℝ)-(v:ℝ)) ((s:ℝ)-(v:ℝ))) r := by
  classical
  by_cases hr : r∈Ioc v b
  · rw [raw,indicator_of_mem (show (r,ω)∈Ioc v b ×ˢ (univ : Set Ω) from ⟨hr,mem_univ _⟩),
      indicator_of_mem hr]
    unfold FrozenReferenceFields.field
    rw [PredictablePastParameter.held_eq data (0,0) hr.1]
    unfold ControlledReferenceEnergy.kernelEnergy
    rw [show (b:ℝ)-(r:ℝ)=((b:ℝ)-(v:ℝ))-((r:ℝ)-(v:ℝ)) by ring]
  · rw [raw,indicator_of_notMem (show (r,ω)∉Ioc v b ×ˢ (univ : Set Ω) from fun h => hr h.1),
      indicator_of_notMem hr]
    simp

/-- Genuine pathwise bracket for ARBITRARY past state maps. The
sample-dependent initial L2 norm remains inside the bound. All relative
time changes and the actual common-Haar reference energy are proved. -/
theorem bracket_bound (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ}
    (hΛ : 0≤Λ) (hκ : κ<P.lower) (θ η : ℝ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (H v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
    (data : Ω → Inputs) (ω : Ω) :
    (∫⁻ r,ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data (r,ω)‖^2) ∂timeMeasure H)≤
      ENNReal.ofReal (HaarReference.rowConstant (P.lower-κ) (P.upper-κ) *
        (2*ProfileStability.meanConstant P.lower P.holder P.exponent)^2 *
        ProfileVolterra.powerConstant ((P.exponent-1)/2)*((b:ℝ)-(v:ℝ))^(P.exponent/2)*
        (|θ-η| * ‖(data ω).2‖)^2) := by
  have htime : 0<(b:ℝ)-(v:ℝ) := sub_pos.mpr (by exact_mod_cast hvb)
  have he := ControlledReferenceEnergy.kernel_time_energy P hΛ hκ (data ω).1 (data ω).2
    θ η hsmall htime hsmallTime
  have hid : (∫⁻ r,ENNReal.ofReal (‖raw P Λ κ θ η hκ v b data (r,ω)‖^2) ∂timeMeasure H)=
      ENNReal.ofReal (∫ s in (0:ℝ)..((b:ℝ)-(v:ℝ)),
        ControlledReferenceEnergy.kernelEnergy P Λ κ hκ (data ω).1 (data ω).2 θ η
          ((b:ℝ)-(v:ℝ)) s) := by
    rw [←PastRelativeEnergy.indicator_lintegral H v b hvb.le hbH _ he.1
      (fun s => sq_nonneg _)]
    apply lintegral_congr
    intro r
    rw [raw_norm_sq]
    by_cases hr : r∈Ioc v b <;> simp [hr]
  rw [hid]
  exact ENNReal.ofReal_le_ofReal he.2

end SHE.PastReferenceBracket
