module

public import SHE.CompanionEnergy
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.CompanionPicard
open MeasureTheory Set PredictableL2 CompanionHeat LowBands
open scoped ENNReal NNReal
local instance companionPicard_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance companionPicard_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance companionPicard_stateBorel : BorelSpace StateL2 := ⟨rfl⟩

section Process
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

abbrev Space := Process (E := StateL2) 𝓕 μ h

/-- The exact standard stochastic isometry for a supplied convolution
map with the literal damped common-Haar nonlinear columns. This is an
explicit standard-input interface, not an assertion that such a map has
already been constructed. No heat estimate is included in this premise. -/
def DampedConvolutionIsometry (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ z,|a z| ≤ M) (Λ : ℝ) (N : Space 𝓕 μ h → Space 𝓕 μ h) : Prop :=
  ∀ u v,ENNReal.ofReal (‖N u-N v‖^2)=
    ∫⁻ t,∫⁻ s,∫⁻ ω,ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
      columnEnergy a ha M hM (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ)))
      ∂μ ∂timeMeasure t ∂timeMeasure h

/-- The actual predictable L² stochastic Picard map contracts on a
proved short horizon. The sole stochastic premise is its exact standard
isometry; every nonlinear heat and time estimate is checked. -/
theorem convolution_lipschitz {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) (hM : ∀ z,|a z| ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) (hh : (h:ℝ) ≤ 1)
    (hsmall : 2*picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (N : Space 𝓕 μ h → Space 𝓕 μ h)
    (hIto : DampedConvolutionIsometry 𝓕 μ h a ha M hM Λ N) : LipschitzWith (1/2) N := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hu : Measurable (fun p : ℝ≥0 × Ω => u p) :=
    (realization_stronglyMeasurable (energyMeasure μ h) (predictable_le_product 𝓕) u).measurable
  have hv : Measurable (fun p : ℝ≥0 × Ω => v p) :=
    (realization_stronglyMeasurable (energyMeasure μ h) (predictable_le_product 𝓕) v).measurable
  have he := expected_damped_causal_column_energy μ ha hell haB hM hLip h hh u v hu hv hΛ
  rw [← hIto u v,← process_difference_lintegral_energy 𝓕 μ h u v] at he
  have hC : 0 ≤ 2*picardConstant ell M L*(h:ℝ)^(1/2:ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (picardConstant_nonneg ((abs_nonneg (a 0)).trans (hM 0)) L))
      (Real.rpow_nonneg h.2 _)
  rw [← ENNReal.ofReal_mul hC] at he
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg ‖u-v‖))).mp he
  have hsq := hreal.trans (mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u-v‖))
  rw [dist_eq_norm,dist_eq_norm]
  change ‖N u-N v‖ ≤ (1/2:ℝ)*‖u-v‖
  nlinarith [norm_nonneg (N u-N v),norm_nonneg (u-v)]

theorem exists_unique_fixedPoint {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) (hM : ∀ z,|a z| ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) (hh : (h:ℝ) ≤ 1)
    (hsmall : 2*picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (N : Space 𝓕 μ h → Space 𝓕 μ h)
    (hIto : DampedConvolutionIsometry 𝓕 μ h a ha M hM Λ N) (forcing : Space 𝓕 μ h) :
    ∃! v : Space 𝓕 μ h,v=forcing+N v := by
  let Φ : Space 𝓕 μ h → Space 𝓕 μ h := fun v => forcing+N v
  have hN := convolution_lipschitz 𝓕 μ h ha hell haB hM hLip hh hsmall hΛ N hIto
  have hΦ : LipschitzWith (1/2) Φ := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [Φ,dist_add_left] using hN.dist_le_mul u v
  have hcon : ContractingWith (1/2) Φ := ⟨by norm_num,hΦ⟩
  refine ⟨hcon.fixedPoint Φ,hcon.fixedPoint_isFixedPt.symm,?_⟩
  intro v hv
  exact hcon.fixedPoint_unique hv.symm

end Process

theorem exists_contraction_horizon {K : ℝ} (hK : 0 ≤ K) :
    ∃ h : ℝ≥0,0 < h ∧ (h:ℝ) ≤ 1 ∧ 2*K*(h:ℝ)^(1/2:ℝ) ≤ 1/4 := by
  let r : ℝ := 1/(8*K+1)
  have hd : 0 < 8*K+1 := by positivity
  have hr : 0 < r := one_div_pos.mpr hd
  have hr1 : r ≤ 1 := (div_le_iff₀ hd).mpr (by nlinarith)
  let h : ℝ≥0 := ⟨r^2,sq_nonneg r⟩
  refine ⟨h,?_,?_,?_⟩
  · change 0 < r^2
    positivity
  · change r^2 ≤ 1
    nlinarith
  · have hs : (h:ℝ)^(1/2:ℝ)=r := by
      change (r^2)^(1/2:ℝ)=r
      rw [← Real.sqrt_eq_rpow,Real.sqrt_sq hr.le]
    rw [hs]
    change 2*K*(1/(8*K+1)) ≤ 1/4
    rw [mul_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith

end SHE.CompanionPicard
