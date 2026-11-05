module

public import SHE.HistorySpatialSections
public import SHE.ActualMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.HistoryProductMeasure
open Set Filter MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω]

/-- Genuine Borel Fubini swaps the physical input point past every old
spatial history coordinate. A family of separately AE fixed-center
claims is never evaluated on an adaptive diagonal. -/
theorem ae_input_sections (R : ReferenceData) (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ)
    (F : History P k × HeatCircle → Prop) (hF : MeasurableSet {z | F z})
    (hAE : ∀ᵐ p ∂historyMeasure R μ k,∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,F (p,y)) :
    ∀ᵐ p ∂μ,∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
      ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
        ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
          F (separated k (p,t,x),y) := by
  filter_upwards [ae_spatial_sections R μ k hAE] with p hp
  filter_upwards [hp] with t ht
  have hm : Measurable (fun z : (Fin k → HeatCircle) × HeatCircle =>
      (separated k (p,t,z.1),z.2)) :=
    ((separated_measurable k).comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
  have hset : MeasurableSet {z : (Fin k → HeatCircle) × HeatCircle | F (separated k (p,t,z.1),z.2)} :=
    hF.preimage hm
  have hjoint := (Measure.ae_prod_iff_ae_ae hset).mpr ht
  have hswapMP : MeasurePreserving
      (Prod.swap : HeatCircle × (Fin k → HeatCircle) → (Fin k → HeatCircle) × HeatCircle)
      ((AddCircle.haarAddCircle : Measure HeatCircle).prod
        (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)))
      ((Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)).prod
        (AddCircle.haarAddCircle : Measure HeatCircle)) := Measure.measurePreserving_swap
  have hswap := hswapMP.quasiMeasurePreserving.ae hjoint
  exact Measure.ae_ae_of_ae_prod hswap

attribute [local irreducible] History historyMeasurableSpace
set_option backward.isDefEq.respectTransparency true

theorem measurable_abs_moment {Y : Type} [MeasurableSpace Y]
    (μ : Measure Ω) [SFinite μ] (K : Ω × Y → ℝ) (hK : Measurable K) (order : ℕ) :
    Measurable (fun y => ∫ ω,|K (ω,y)|^order ∂μ) := by
  have hm : Measurable (fun z : Y × Ω => |K (z.2,z.1)|^order) :=
    (continuous_abs.measurable.comp (hK.comp (measurable_snd.prodMk measurable_fst))).pow_const order
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable

/-- Exchange a genuine root/time/input event before fixing the old time
section. In particular, a time-dependent heat-row choice is not inserted
into a separately AE fixed-time assertion. -/
theorem ae_parameter_swap {B Y : Type} [MeasurableSpace B] [MeasurableSpace Y]
    (μ : Measure P) [SFinite μ] (ν : Measure B) [SFinite ν] (κ : Measure Y) [SFinite κ]
    (F : P × (B × Y) → Prop) (hF : MeasurableSet {z | F z})
    (hAE : ∀ᵐ p ∂μ,∀ᵐ t ∂ν,∀ᵐ y ∂κ,F (p,t,y)) :
    ∀ᵐ t ∂ν,∀ᵐ p ∂μ,∀ᵐ y ∂κ,F (p,t,y) := by
  have hall : ∀ᵐ z ∂μ.prod (ν.prod κ),F z := by
    apply (Measure.ae_prod_iff_ae_ae hF).mpr
    filter_upwards [hAE] with p hp
    have hFp : MeasurableSet {z : B × Y | F (p,z)} :=
      hF.preimage (measurable_const.prodMk measurable_id)
    exact (Measure.ae_prod_iff_ae_ae hFp).mpr hp
  have hmp := (measurePreserving_prodAssoc μ ν κ).comp
    (((Measure.measurePreserving_swap (μ:=ν) (ν:=μ)).prod (MeasurePreserving.id κ)).comp
      (measurePreserving_prodAssoc ν μ κ).symm)
  have hswap := hmp.quasiMeasurePreserving.ae hall
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with t ht
  exact Measure.ae_ae_of_ae_prod ht


end SHE.HistoryProductMeasure
