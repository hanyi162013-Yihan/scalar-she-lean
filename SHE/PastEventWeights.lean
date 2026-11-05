module

public import SHE.RealMomentBound
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.PastEventWeights
open Set MeasureTheory
variable {Ω : Type*} {m m0 : MeasurableSpace Ω}

/-- Bounds on EVERY event in a smaller sigma algebra imply domination
of the actual density measure after restriction to that sigma algebra. -/
theorem density_trim_le (μ : @Measure Ω m0) [IsFiniteMeasure μ] (hm : m≤m0)
    (f : Ω→ℝ) (hf : Integrable f μ) (hpos : ∀ ω,0≤f ω) (C : ℝ) (hC : 0≤C)
    (hb : ∀ A,MeasurableSet[m] A → (∫ ω in A,f ω ∂μ)≤C*μ.real A) :
    (μ.withDensity (fun ω=>ENNReal.ofReal (f ω))).trim hm≤ENNReal.ofReal C • μ.trim hm := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [trim_measurableSet_eq hm hA,withDensity_apply _ (hm A hA),Measure.smul_apply,
    trim_measurableSet_eq hm hA]
  rw [←ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hpos)]
  calc
    ENNReal.ofReal (∫ ω in A,f ω ∂μ)≤ENNReal.ofReal (C*μ.real A) := ENNReal.ofReal_le_ofReal (hb A hA)
    _=ENNReal.ofReal C*μ A := by rw [ENNReal.ofReal_mul hC,ofReal_measureReal]

/-- Conditional moment event bounds extend to ANY integrable
nonnegative past-measurable weight. In particular the actual random
past input energy can remain correlated with all later variables. -/
theorem weighted_integral (μ : @Measure Ω m0) [IsFiniteMeasure μ] (hm : m≤m0)
    (f : Ω→ℝ) (hf : Measurable[m0] f) (hfi : Integrable f μ) (hpos : ∀ ω,0≤f ω)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀ A,MeasurableSet[m] A → (∫ ω in A,f ω ∂μ)≤C*μ.real A)
    (g : Ω→ℝ) (hg : Measurable[m] g) (hg0 : ∀ ω,0≤g ω) (hgi : Integrable g μ) :
    Integrable (fun ω=>g ω*f ω) μ ∧ (∫ ω,g ω*f ω ∂μ)≤C*(∫ ω,g ω ∂μ) := by
  have hdom := density_trim_le μ hm f hfi hpos C hC hb
  have hgm : Measurable[m0] g := hg.mono hm le_rfl
  have he : (∫⁻ ω,ENNReal.ofReal (g ω*f ω) ∂μ)=
      ∫⁻ ω,ENNReal.ofReal (g ω) ∂μ.withDensity (fun ω=>ENNReal.ofReal (f ω)) := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hf.ennreal_ofReal hgm.ennreal_ofReal]
    apply lintegral_congr
    intro ω
    simp only [Pi.mul_apply,ENNReal.ofReal_mul (hg0 ω)]
    exact mul_comm _ _
  have hh : (∫⁻ ω,ENNReal.ofReal (g ω*f ω) ∂μ)≤ENNReal.ofReal (C*(∫ ω,g ω ∂μ)) := by
    rw [he,←lintegral_trim hm hg.ennreal_ofReal]
    calc
      _≤∫⁻ ω,ENNReal.ofReal (g ω) ∂(ENNReal.ofReal C • μ.trim hm) := lintegral_mono' hdom le_rfl
      _=ENNReal.ofReal (C*(∫ ω,g ω ∂μ)) := by
        rw [lintegral_smul_measure,lintegral_trim hm hg.ennreal_ofReal,
          ←ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),ENNReal.ofReal_mul hC]
        rfl
  exact RealMomentBound.integral_bound μ _ (hgm.mul hf).aestronglyMeasurable
    (fun ω=>mul_nonneg (hg0 ω) (hpos ω)) (mul_nonneg hC (integral_nonneg hg0)) hh

end SHE.PastEventWeights
