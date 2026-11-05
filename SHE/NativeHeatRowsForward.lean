module

public import SHE.NativeObservationCovariance
public import SHE.NativeMultiplierColumnFields
public import SHE.NativeBesselReal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.NativeHeatRowsForward
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation NativeObservationCovariance FiniteHaar
open scoped NNReal ENNReal
local instance nativeHeatRowsForward_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeHeatRowsForward_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- Literal original common-Haar observation coordinates are the
forward native heat columns, on one spatial event for every countable
noise coordinate. This is the physical row/column identification. -/
theorem row_column_ae {ell M T q : ℝ} (hell : 0<ell) (f : EllipticField ell M)
    (hq : q<T) (i : HaarNode) :
    (fun x : HeatCircle=>(row hell f T q x i : ℂ))=ᵐ[haarAddCircle]
      (circleHeatOperator (T-q) (sub_pos.mpr hq).le
        (CircleNormalization.push (globalHaarColumn i f.1)) : HeatCircle→ℂ) := by
  have ht : 0<T-q:=sub_pos.mpr hq
  filter_upwards [heat_kernel_inner_ae ht (CircleNormalization.push (globalHaarColumn i f.1))] with x hx
  rw [←hx]
  have he:=CircleNormalization.push.inner_map_map (globalHaarColumn i f.1)
    (CircleNormalization.push.symm (circleHeat (T-q) x))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  have hr:=analysis_heat_real hell f hq x i
  change (inner ℂ (globalHaarColumn i f.1) (CircleNormalization.push.symm (circleHeat (T-q) x))).im=0 at hr
  have hz : (row hell f T q x i : ℂ)=
      inner ℂ (globalHaarColumn i f.1) (CircleNormalization.push.symm (circleHeat (T-q) x)) := by
    change (((inner ℂ (globalHaarColumn i f.1) (CircleNormalization.push.symm (circleHeat (T-q) x))).re : ℝ):ℂ)=_
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hr.symm
  rw [hz,←he]
  have hi : (inner ℂ (CircleNormalization.push (globalHaarColumn i f.1)) (circleHeat (T-q) x)).im=0 := by
    rw [he]
    exact hr
  have hs:=inner_conj_symm (𝕜:=ℂ) (circleHeat (T-q) x) (CircleNormalization.push (globalHaarColumn i f.1))
  apply Complex.ext
  · simpa only [Complex.conj_re] using (congrArg Complex.re hs)
  · have hs':=congrArg Complex.im hs
    simp only [Complex.conj_im,hi] at hs'
    linarith

/-- One physical gradient/noise product, in the SAME original Haar
coordinates, equals its actual native multiplier/heat column. -/
theorem multiplier_row_ae {P : Type*} [MeasurableSpace P]
    {ell M T q : ℝ} (hell : 0<ell) (f : EllipticField ell M) (hq : q<T)
    {b : P×HeatCircle→ℂ} (hbm : Measurable b) (cap : P→ℝ)
    (hb : ∀ p x,‖b (p,x)‖≤cap p) (p : P) (i : HaarNode) :
    (NativeMultiplierTrace.multiplier (NativeRandomRows.nativeRow b p) (cap p)
      (NativeMultiplierColumnFields.row_bound hbm cap hb p)
      (circleHeatOperator (T-q) (sub_pos.mpr hq).le
        (CircleNormalization.push (globalHaarColumn i f.1))) : HeatCircle→ℂ)=ᵐ[haarAddCircle]
      fun x=>b (p,x)*(row hell f T q x i : ℂ) := by
  filter_upwards [NativeMultiplierTrace.multiplier_ae (NativeRandomRows.nativeRow b p) (cap p)
      (NativeMultiplierColumnFields.row_bound hbm cap hb p)
      (circleHeatOperator (T-q) (sub_pos.mpr hq).le (CircleNormalization.push (globalHaarColumn i f.1))),
    NativeRandomRows.nativeRow_ae_cap hbm cap hb p,row_column_ae hell f hq i] with x hm hb hr
  rw [hm,hb,←hr]

end SHE.NativeHeatRowsForward
