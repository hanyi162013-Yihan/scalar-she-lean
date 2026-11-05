module

public import SHE.HaarKernelL2Approximation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarKernelL2Approximation
open MeasureTheory Set Filter PredictableL2 HaarKernelApproximation
open scoped NNReal ENNReal Topology
local instance haarKernelPairConvergence_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance haarKernelPairConvergence_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarKernelPairConvergence_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance haarKernelPairConvergence_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance haarKernelPairConvergence_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarKernelPairConvergence_columnsBorel : BorelSpace Columns := ⟨rfl⟩

/-- The exact squared difference energy of two genuine common-Haar
coefficient fields is preserved in the finite time-cell limit. -/
theorem pair_energy_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M} (hf : Measurable f) (hg : Measurable g) :
    Tendsto (fun n => ∫⁻ p,ENNReal.ofReal (‖approx hell f n p-approx hell g n p‖^2) ∂measure μ h)
      atTop (𝓝 (∫⁻ p,ENNReal.ofReal (‖raw hell f p-raw hell g p‖^2) ∂measure μ h)) := by
  have hfm : Measurable (fun p => ENNReal.ofReal (‖raw hell f p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((raw_measurable hell hf).norm.pow_const 2)
  have hgm : Measurable (fun p => ENNReal.ofReal (‖raw hell g p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((raw_measurable hell hg).norm.pow_const 2)
  have htime : ∀ᵐ p ∂measure μ h,0 < p.1 :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem h).mono (fun _ ht => ht.1))
  have hfinite : (∫⁻ p,(2:ℝ≥0∞)*(ENNReal.ofReal (‖raw hell f p‖^2)+
      ENNReal.ofReal (‖raw hell g p‖^2)) ∂measure μ h) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ (by norm_num),lintegral_add_left hfm]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr ⟨(raw_energy_finite hell hM μ h hh hf).ne,
        (raw_energy_finite hell hM μ h hh hg).ne⟩)
  apply tendsto_lintegral_of_dominated_convergence
    (fun p => (2:ℝ≥0∞)*(ENNReal.ofReal (‖raw hell f p‖^2)+ENNReal.ofReal (‖raw hell g p‖^2)))
  · intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      (((approx_measurable hell hf n).sub (approx_measurable hell hg n)).norm.pow_const 2)
  · intro n
    filter_upwards [htime] with p hp
    have hfn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (approximant_norm_sq_le (t := p.1) (s := p.2.1) hell (by exact_mod_cast hp) (f p.2) n)
    have hgn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (approximant_norm_sq_le (t := p.1) (s := p.2.1) hell (by exact_mod_cast hp) (g p.2) n)
    have htri := norm_sub_le (approx hell f n p) (approx hell g n p)
    have hsq : ‖approx hell f n p-approx hell g n p‖^2 ≤
        2*(‖raw hell f p‖^2+‖raw hell g p‖^2) := by
      change ‖approx hell f n p‖ ≤ ‖raw hell f p‖ at hfn
      change ‖approx hell g n p‖ ≤ ‖raw hell g p‖ at hgn
      nlinarith [norm_nonneg (approx hell f n p-approx hell g n p),
        norm_nonneg (raw hell f p),norm_nonneg (raw hell g p),
        sq_nonneg (‖raw hell f p‖-‖raw hell g p‖)]
    have hb := ENNReal.ofReal_le_ofReal hsq
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),ENNReal.ofReal_ofNat] using hb
  · exact hfinite
  · filter_upwards [htime] with p hp
    have hf' := approximant_tendsto (t := p.1) (s := p.2.1) hell (by exact_mod_cast hp) (f p.2)
    have hg' := approximant_tendsto (t := p.1) (s := p.2.1) hell (by exact_mod_cast hp) (g p.2)
    have hsub : Tendsto (fun n => approx hell f n p-approx hell g n p) atTop
        (𝓝 (raw hell f p-raw hell g p)) := hf'.sub hg'
    have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hsub.norm.pow 2)
    change Tendsto (fun n => ENNReal.ofReal (‖approx hell f n p-approx hell g n p‖^2))
      atTop (𝓝 (ENNReal.ofReal (‖raw hell f p-raw hell g p‖^2))) at hn
    exact hn

end SHE.HaarKernelL2Approximation
