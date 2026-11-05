module

public import SHEStochastic.EnergyClipping

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.UniformEnergyBound
open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- A bounded low-energy part and the actual tail control the full
expectation, without assuming integrability in advance. -/
theorem split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : Ω → ℝ) (he : Measurable e) (R : ℝ) :
    (∫⁻ x,ENNReal.ofReal (e x) ∂μ)≤ENNReal.ofReal R+
      (∫⁻ x in {x | R≤e x},ENNReal.ofReal (e x) ∂μ) := by
  rw [←lintegral_add_compl (fun x => ENNReal.ofReal (e x)) (measurableSet_le measurable_const he)]
  rw [add_comm (ENNReal.ofReal R)]
  apply add_le_add le_rfl
  calc
    _ ≤ ∫⁻ x in {x | R≤e x}ᶜ,ENNReal.ofReal R ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const he).compl] with x hx
      exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hx))
    _ = ENNReal.ofReal R*μ {x | R≤e x}ᶜ := by rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal R*1 := mul_le_mul_right (prob_le_one (μ := μ)) _
    _ = _ := mul_one _

/-- Uniformly vanishing energy tails imply a common finite energy
expectation, including integrability on all varying source spaces. -/
theorem exists_bound {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    (P : ∀ m,Measure (Ω m)) [∀ m,IsProbabilityMeasure (P m)]
    (e : ∀ m,Ω m → ℝ) (he : ∀ m,Measurable (e m)) (hnonneg : ∀ m x,0≤e m x)
    (hUI : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤e m x},ENNReal.ofReal (e m x) ∂P m)
      atTop (𝓝 0)) :
    ∃ C : ℝ,0≤C ∧ ∀ m,Integrable (e m) (P m) ∧ (∫ x,e m x ∂P m)≤C := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hUI.eventually_lt_const (by norm_num : (0 : ℝ≥0∞)<1))
  let R : ℕ := N+1
  have htail (m : ℕ) : (∫⁻ x in {x | (R : ℝ)≤e m x},ENNReal.ofReal (e m x) ∂P m)≤1 :=
    (le_iSup (fun j => ∫⁻ x in {x | (R : ℝ)≤e j x},ENNReal.ofReal (e j x) ∂P j) m).trans
      (hN R (by dsimp only [R];omega)).le
  have hb (m : ℕ) : (∫⁻ x,ENNReal.ofReal (e m x) ∂P m)≤ENNReal.ofReal ((R : ℝ)+1) := by
    apply (split (P m) (e m) (he m) (R : ℝ)).trans
    rw [ENNReal.ofReal_add (Nat.cast_nonneg R) (by norm_num : (0 : ℝ)≤1),ENNReal.ofReal_one]
    exact add_le_add le_rfl (htail m)
  refine ⟨(R : ℝ)+1,by positivity,fun m => ?_⟩
  have hi : Integrable (e m) (P m) :=
    (lintegral_ofReal_ne_top_iff_integrable (he m).aestronglyMeasurable
      (Filter.Eventually.of_forall (hnonneg m))).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb m))
  refine ⟨hi,?_⟩
  have hh := hb m
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hnonneg m)),
    ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ)≤(R : ℝ)+1)] at hh
  exact hh

end SHEStochastic.UniformEnergyBound
