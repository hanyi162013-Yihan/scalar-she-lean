module

public import SHE.ControlledScalarCovarianceTailEnergy
public import SHE.NativeCanonicalReferenceField
public import SHE.ScalarCanonicalVariance

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeCanonicalVarianceField
open scoped NNReal ENNReal
open Set MeasureTheory ControlledProfile StoppedFourier DyadicApproximation NativeHeatObservation
local instance nativeCanonicalVarianceField_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalVarianceField_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCanonicalVarianceField_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCanonicalVarianceField_nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCanonicalVarianceField_nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable (P : CanonicalCovariance.ProfileParameters) (Λ θ : ℝ) (v b : ℝ≥0)
variable (u d : Ω→RealL2) (hu : Measurable[𝓕 v] u) (hd : Measurable[𝓕 v] d)

def field (p : (ℝ≥0×Ω)×HeatCircle) : ℝ:=
  ControlledScalarCovarianceTailEnergy.field P Λ v b θ
    ((PredictablePastParameter.held v (NativeCanonicalReferenceField.data u d) (0,0) p.1,p.1.1),p.2)

include hu hd in
/-- The true own-profile remaining variance is jointly predictable in
current time/sample and Borel in the native root. The whole future
profile is F_v-data, legitimately held only after v. -/
theorem field_predictable :
    @Measurable ((ℝ≥0×Ω)×HeatCircle) ℝ (𝓕.predictable.prod inferInstance) _
      (field P Λ θ v b u d) := by
  have hp:=PredictablePastParameter.held_measurable 𝓕 v (NativeCanonicalReferenceField.data u d)
    (NativeCanonicalReferenceField.data_measurable 𝓕 v u d hu hd) (0,0)
  have ht:=PredictableClock.real_time_measurable 𝓕
  exact (ControlledScalarCovarianceTailEnergy.field_measurable P Λ v b θ).comp
    (((hp.comp measurable_fst).prodMk (ht.comp measurable_fst)).prodMk measurable_snd)

theorem field_eq (q : ℝ≥0) (hvq : v<q) (hqb : q≤b) (ω : Ω) (x : HeatCircle) :
    field P Λ θ v b u d ((q,ω),x)=ControlledScalarCovarianceTail.tail P Λ v q b θ
      (embed (u ω)) (embed (d ω)) x := by
  simp only [field,ControlledScalarCovarianceTailEnergy.field,
    PredictablePastParameter.held_eq (p:=(q,ω)) _ _ hvq,
    min_eq_left (show (q:ℝ)≤(b:ℝ) by exact_mod_cast hqb),NativeCanonicalReferenceField.data]

/-- The actual variance has its genuine uniform sqrt-age lower bound,
not a fixed positive reserve or a supplied ellipticity premise. -/
theorem lower (q : ℝ≥0) (hvq : v<q) (hqb : q<b) (hb1 : (b:ℝ)≤1) (ω : Ω) (x : HeatCircle) :
    ProfileVariance.lowerConstant*P.lower*((b:ℝ)-(q:ℝ))^(1/2:ℝ)≤
      field P Λ θ v b u d ((q,ω),x) := by
  rw [field_eq P Λ θ v b u d q hvq hqb.le ω x]
  apply (ScalarCovarianceTailScale.elliptic
    (ControlledReferenceWindows.coefficient_section_measurable P Λ θ v (embed (u ω),embed (d ω)))
    (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb)
    ((sub_le_self _ q.coe_nonneg).trans hb1) P.lower_pos.le P.upper_nonneg
    (ControlledReferenceWindows.coefficient_bounds P Λ θ v (embed (u ω),embed (d ω))) x).1

end SHE.NativeCanonicalVarianceField
