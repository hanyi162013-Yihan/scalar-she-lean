module

public import SHE.NativeObservationCovariance
public import SHE.HaarDamping
public import SHE.HilbertColumns
public import SHE.PhysicalMeanSemigroup

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativePhysicalRowFields
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance
open scoped ENNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩

/-- Each physical analysis coordinate is the genuine heat average of
its same-Haar column, including the zero extension at nonpositive age. -/
theorem row_apply {ell M : ℝ} (hell : 0<ell) (f : FiniteHaar.EllipticField ell M)
    (a : ℝ) (x : HeatCircle) (q : HaarNode) :
    row hell f a 0 x q = if 0<a then
      PhysicalProfile.physicalHeatMean (CircleNormalization.push (globalHaarColumn q f.1)) (a,x) else 0 := by
  by_cases ha : 0<a
  · rw [ite_eq_left ha,PhysicalProfile.physicalHeatMean_eq ha]
    change (inner ℂ (globalHaarColumn q f.1)
      (CircleNormalization.push.symm (circleHeat (a-0) x))).re = _
    rw [sub_zero]
    have he := CircleNormalization.push.inner_map_map (globalHaarColumn q f.1)
      (CircleNormalization.push.symm (circleHeat a x))
    rw [LinearIsometryEquiv.apply_symm_apply] at he
    rw [← he]
    simpa only [Complex.conj_re] using congrArg Complex.re (inner_conj_symm (circleHeat a x)
      (CircleNormalization.push (globalHaarColumn q f.1)))
  · simp only [ite_eq_right ha]
    change (inner ℂ (globalHaarColumn q f.1)
      (CircleNormalization.push.symm (circleHeat (a-0) x))).re=0
    simp only [sub_zero,circleHeat,dite_eq_right ha,map_zero,inner_zero_right,Complex.zero_re]

/-- Joint Borel dependence of the literal infinite analysis row on its
coefficient, age and spatial center, proved coordinate by coordinate. -/
theorem row_measurable (ell M : ℝ) (hell : 0<ell) :
    Measurable (fun p : FiniteHaar.EllipticField ell M×(ℝ×HeatCircle) =>
      row hell p.1 p.2.1 0 p.2.2) := by
  apply HilbertColumns.measurable_of_columns
  intro q
  have hc : Measurable (fun p : FiniteHaar.EllipticField ell M×(ℝ×HeatCircle) =>
      globalHaarColumn q p.1.1) :=
    (FiniteHaar.measurable_globalHaarColumn q).comp measurable_fst.subtype_val
  have hp := CircleNormalization.push.continuous.measurable.comp hc
  have hm := PhysicalProfile.physicalHeatMean_joint_measurable.comp (hp.prodMk measurable_snd)
  have he : Measurable (fun p : FiniteHaar.EllipticField ell M×(ℝ×HeatCircle) =>
      if 0<p.2.1 then PhysicalProfile.physicalHeatMean
        (CircleNormalization.push (globalHaarColumn q p.1.1)) p.2 else (0:ℝ)) :=
    hm.ite (measurableSet_lt measurable_const measurable_snd.fst) measurable_const
  simpa only [row_apply hell] using he

/-- The target and current time are independent parameters of this row. -/
theorem row_measurable_comp {P : Type*} [MeasurableSpace P] {ell M : ℝ} (hell : 0<ell)
    {f : P→FiniteHaar.EllipticField ell M} (hf : Measurable f)
    {T r : P→ℝ} (hT : Measurable T) (hr : Measurable r)
    {x : P→HeatCircle} (hx : Measurable x) :
    Measurable (fun p => row hell (f p) (T p) (r p) (x p)) := by
  have hm := (row_measurable ell M hell).comp (hf.prodMk ((hT.sub hr).prodMk hx))
  convert hm using 1
  funext p
  simp only [row,sub_zero,Pi.sub_apply,Function.comp_apply]

end SHE.NativePhysicalRowFields
