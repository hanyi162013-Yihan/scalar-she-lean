module
public import SHE.PredictableTime
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.ClockSquareRestriction
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[SFinite μ]

/-- A full real-clock L2 bound restricts to the ORIGINAL nonnegative
predictable output clock, with no normalization or horizon loss. -/
theorem energy (H:ℝ≥0)(F:ℝ×Ω→ℝ)
    (hi:Integrable (fun z=>F z^2) (volume.prod μ)):
    Integrable (fun z:ℝ≥0×Ω=>F ((z.1:ℝ),z.2)^2) (energyMeasure μ H) ∧
      (∫z:ℝ≥0×Ω,F ((z.1:ℝ),z.2)^2 ∂energyMeasure μ H)≤
        ∫z:ℝ×Ω,F z^2 ∂volume.prod μ:=by
  let η:Measure (ℝ×Ω):=(volume.restrict (Ioc (0:ℝ) (H:ℝ))).prod μ
  have hη:η≤volume.prod μ:=Measure.prod_mono Measure.restrict_le_self le_rfl
  have hlocal:Integrable (fun z:ℝ×Ω=>F z^2) η:=hi.mono_measure hη
  have hp:MeasurePreserving (fun z:ℝ≥0×Ω=>((z.1:ℝ),z.2)) ((timeMeasure H).prod μ) η:=
    (timeMeasurePreserving H).prod (MeasurePreserving.id μ)
  have hN:Integrable (fun z:ℝ≥0×Ω=>F ((z.1:ℝ),z.2)^2) ((timeMeasure H).prod μ):=
    (hp.integrable_comp hlocal.aestronglyMeasurable).mpr hlocal
  have he:(∫z:ℝ≥0×Ω,F ((z.1:ℝ),z.2)^2 ∂((timeMeasure H).prod μ))=
      ∫z:ℝ×Ω,F z^2 ∂η:=by
    rw [integral_prod _ hN,timeMeasure_integral,integral_prod _ hlocal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.coe_toNNReal _ ht.1.le]
  refine ⟨hN,?_⟩
  change (∫z:ℝ≥0×Ω,F ((z.1:ℝ),z.2)^2 ∂((timeMeasure H).prod μ))≤_
  rw [he]
  exact integral_mono_measure hη (ae_of_all _ (fun z=>sq_nonneg (F z))) hi

end SHE.ClockSquareRestriction
