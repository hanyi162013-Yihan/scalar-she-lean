module
public import SHE.DefectOriginalConvolution
public import SHE.DefectGapDensityMass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
namespace SHE.DefectOldTimeMass
open Set MeasureTheory Real AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
  PhysicalParentGeometry HistoryProductMeasure OrderedGapCoordinates
open scoped BigOperators
open Classical
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)

def weight (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(A0 ν:ℝ)(t:Fin k→ℝ):ℝ:=
  if StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0)) then
    DefectOriginalConvolution.oldFactor L P ell C k t A0 ν else 0

theorem eq_gap (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (T:ℝ)(hT:∀x,L.terminal x=T)(hpos:R.base<T)
    (k:ℕ)(A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν):
    weight L P ell C k A0 ν=
      fun t:Fin k→ℝ=>DefectGapDensity.density P ell C k (T-R.base) A0 ν (gaps T k t):=by
  funext t
  have hi:=StrictHistoryOrder.iff_ordered L T hT hpos k t (0:HeatCircle) (fun _=>0)
  rw [ordered_iff] at hi
  by_cases hp:StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0))
  · have hd:=hi.mp hp
    simp only [weight,DefectGapDensity.density,if_pos hp,if_pos hd]
    exact DefectGapDensity.actual L P ell C R.base T hT k t (0:HeatCircle) (fun _=>0) hp hA0 hν
  · have hd:¬((∀i,0<gaps T k t i) ∧ (∑i,gaps T k t i)<T-R.base):=fun h=>hp (hi.mpr h)
    simp only [weight,DefectGapDensity.density,if_neg hp,if_neg hd]

/-- Complete old-time L1 of the original score/bounded-empty factor,
with its actual assignment/rootMass bound and no collision cutoff. -/
theorem mass (P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(T:ℝ)(hT:∀x,L.terminal x=T)(hpos:R.base<T)
    (k:ℕ)(A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν):
    Measurable (weight L P ell C k A0 ν) ∧
      (∀t,0≤weight L P ell C k A0 ν t) ∧
      Integrable (weight L P ell C k A0 ν)
        (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
      (∫t:Fin k→ℝ,weight L P ell C k A0 ν t
        ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
          DefectGapDensity.mass P ell C k (T-R.base) A0 ν:=by
  have he:=eq_gap L P ell C T hT hpos k A0 ν hA0 hν
  have hm:Measurable (weight L P ell C k A0 ν):=by
    rw [he]
    exact (DefectGapDensity.density_measurable P ell C k (T-R.base) A0 ν).comp (gaps_measurable T k)
  have hn(t:Fin k→ℝ):0≤weight L P ell C k A0 ν t:=by
    rw [he]
    exact DefectGapDensity.density_nonneg P hell C hC k hA0 hν _
  have hD:=DefectGapDensityMass.integral P hell (sub_pos.mpr hpos) C hC k hA0 hν
  have heq:weight L P ell C k A0 ν=fun t:Fin k→ℝ=>if ordered R.base T k t then
      DefectGapDensity.raw P ell C k A0 ν (gaps T k t) else 0:=by
    rw [he]
    funext t
    simp only [DefectGapDensity.density,ordered_iff]
  have hTH:T≤R.horizon:=by simpa only [hT] using L.terminal_horizon (0:HeatCircle)
  have hi:Integrable (weight L P ell C k A0 ν)
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))):=by
    rw [heq]
    apply (PhysicalOrderedGaps.ordered_box_integrable_iff (le_rfl:R.base≤R.base) hTH k _).mpr
    exact (OrderedGapCoordinates.ordered_integrable_iff R.base T k _).mpr hD.1
  refine ⟨hm,hn,hi,?_⟩
  rw [heq,PhysicalOrderedGaps.ordered_box_integral (le_rfl:R.base≤R.base) hTH]
  have hg:=OrderedGapCoordinates.ordered_integral R.base T k (DefectGapDensity.raw P ell C k A0 ν)
  rw [hg]
  exact hD.2
end SHE.DefectOldTimeMass
