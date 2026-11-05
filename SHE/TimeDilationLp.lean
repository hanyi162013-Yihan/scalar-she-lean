module

public import SHE.TimeDilationMeasure
public import SHE.ScaledLpPull

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set Filter PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

def predictableEquiv (e : ℝ≥0≃oℝ≥0) :
    @MeasurableEquiv (ℝ≥0×Ω) (ℝ≥0×Ω) 𝓕.predictable (filtration 𝓕 e).predictable :=
  @MeasurableEquiv.mk _ _ 𝓕.predictable (filtration 𝓕 e).predictable
    (e.toEquiv.prodCongr (Equiv.refl Ω)) (measurable_forward 𝓕 e) (measurable_backward 𝓕 e)

def ambientEquiv : (ℝ≥0×Ω)≃ᵐ(ℝ≥0×Ω) where
  toEquiv := (clock c hc).toEquiv.prodCongr (Equiv.refl Ω)
  measurable_toFun := ((clock_continuous c hc).measurable.comp measurable_fst).prodMk measurable_snd
  measurable_invFun := ((clock_symm_continuous c hc).measurable.comp measurable_fst).prodMk measurable_snd

theorem predictableMeasure_clock_preserving :
    @MeasurePreserving (ℝ≥0×Ω) (ℝ≥0×Ω) 𝓕.predictable (filtration 𝓕 (clock c hc)).predictable
      (fun p => (clock c hc p.1,p.2))
      (ENNReal.ofReal (c:ℝ) • (energyMeasure μ h).trim (predictable_le_product 𝓕))
      ((energyMeasure μ (c*h)).trim (predictable_le_product (filtration 𝓕 (clock c hc)))) := by
  refine @MeasurePreserving.mk _ _ 𝓕.predictable (filtration 𝓕 (clock c hc)).predictable _ _ _
    (measurable_forward 𝓕 (clock c hc)) ?_
  apply @Measure.ext (ℝ≥0×Ω) (filtration 𝓕 (clock c hc)).predictable
  intro S hS
  rw [@Measure.map_apply _ _ 𝓕.predictable (filtration 𝓕 (clock c hc)).predictable _ _
    (measurable_forward 𝓕 (clock c hc)) _ hS,Measure.smul_apply,
    trim_measurableSet_eq (predictable_le_product 𝓕) ((measurable_forward 𝓕 (clock c hc)) hS),
    trim_measurableSet_eq (predictable_le_product (filtration 𝓕 (clock c hc))) hS]
  have hh := congrArg (fun ν : Measure (ℝ≥0×Ω) => ν S) (energyMeasure_clock_preserving c hc h μ).map_eq
  have hm : Measurable (fun p : ℝ≥0×Ω => (clock c hc p.1,p.2)) :=
    ((clock_continuous c hc).measurable.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hm
    ((predictable_le_product (filtration 𝓕 (clock c hc))) S hS),Measure.smul_apply] at hh
  exact hh

/-- Exact normalized pull of physical-clock predictable L² inputs to
the unit-clock input space. Its Jacobian is the literal `sqrt(c)`. -/
def processIsometry : Process (E := E) (filtration 𝓕 (clock c hc)) μ (c*h)→ₗᵢ[ℝ]
    Process (E := E) 𝓕 μ h :=
  @ScaledLpPull.isometry (ℝ≥0×Ω) (ℝ≥0×Ω) E 𝓕.predictable
    (filtration 𝓕 (clock c hc)).predictable _ _
    ((energyMeasure μ h).trim (predictable_le_product 𝓕))
    ((energyMeasure μ (c*h)).trim (predictable_le_product (filtration 𝓕 (clock c hc))))
    (c:ℝ) hc (fun p => (clock c hc p.1,p.2))
    (predictableMeasure_clock_preserving 𝓕 μ c hc h)
    (@MeasurableEquiv.measurableEmbedding _ _ 𝓕.predictable (filtration 𝓕 (clock c hc)).predictable
      (predictableEquiv 𝓕 (clock c hc)))

theorem processIsometry_ae (v : Process (E := E) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    processIsometry 𝓕 μ c hc h v=ᵐ[energyMeasure μ h]
      (fun p => Real.sqrt (c:ℝ) • v (clock c hc p.1,p.2)) := by
  apply ae_eq_of_ae_eq_trim
  exact @ScaledLpPull.pull_ae (ℝ≥0×Ω) (ℝ≥0×Ω) E 𝓕.predictable
    (filtration 𝓕 (clock c hc)).predictable _ _
    ((energyMeasure μ h).trim (predictable_le_product 𝓕))
    ((energyMeasure μ (c*h)).trim (predictable_le_product (filtration 𝓕 (clock c hc))))
    (c:ℝ) hc (fun p => (clock c hc p.1,p.2)) (predictableMeasure_clock_preserving 𝓕 μ c hc h) v

theorem processIsometry_stopped (l : ℝ≥0)
    (v : Process (E := E) (filtration 𝓕 (clock c hc)) μ (c*h))
    (hv : ∀ᵐ p ∂energyMeasure μ (c*h),l<p.1→v p=0) :
    ∀ᵐ p ∂energyMeasure μ h,(clock c hc).symm l<p.1→processIsometry 𝓕 μ c hc h v p=0 := by
  have hh := (energyMeasure_clock_preserving c hc h μ).quasiMeasurePreserving.ae hv
  have hh' := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp hh
  filter_upwards [processIsometry_ae 𝓕 μ c hc h v,hh'] with p hp hs hlt
  have hlt' : l<clock c hc p.1 := by
    simpa only [OrderIso.apply_symm_apply] using (clock c hc).strictMono hlt
  rw [hp,hs hlt',smul_zero]

end SHE.PredictableTimeDilation
