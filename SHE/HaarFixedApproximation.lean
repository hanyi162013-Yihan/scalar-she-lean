module

public import SHE.HaarItoApproximation
public import SHE.TerminalHaarConvolution
public import SHE.EnergyConvergence

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HaarFixedApproximation
open MeasureTheory Set Filter PredictableL2 CircleHeat FiniteHaar HaarKernelApproximation HaarKernelL2Approximation
open scoped NNReal ENNReal Topology
local instance haarFixedApproximation_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarFixedApproximation_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance haarFixedApproximation_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance haarFixedApproximation_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarFixedApproximation_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩
local instance haarFixedApproximation_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarFixedApproximation_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1) {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

def error (t : ℝ≥0) (n : ℕ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (‖approx hell f n (t,p)-raw hell f (t,p)‖^2) ∂energyMeasure μ h

include hh hM hf in
theorem error_tendsto (t : ℝ≥0) (ht : 0 < t) (hth : t ≤ h) :
    Tendsto (error μ h hell f t) atTop (𝓝 0) := by
  have hf0 := (hf.mono (predictable_le_product 𝓕)).measurable
  have hraw : Measurable (fun p => raw hell f (t,p)) :=
    (raw_measurable hell hf0).comp (measurable_const.prodMk measurable_id)
  have happrox (n : ℕ) : Measurable (fun p => approx hell f n (t,p)) :=
    (approx_measurable hell hf0 n).comp (measurable_const.prodMk measurable_id)
  have hnorm : Measurable (fun p => ENNReal.ofReal (‖raw hell f (t,p)‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp (hraw.norm.pow_const 2)
  have hE : (∫⁻ p,ENNReal.ofReal (‖raw hell f (t,p)‖^2) ∂energyMeasure μ h) < ∞ := by
    change (∫⁻ p,ENNReal.ofReal (‖raw hell f (t,p)‖^2) ∂(timeMeasure h).prod μ) < ∞
    rw [lintegral_prod _ hnorm.aemeasurable]
    exact (HaarFixedTerminalEnergy.fixed_energy_bound μ hell hM hh hth f).trans_lt ENNReal.ofReal_lt_top
  have hfinite : (∫⁻ p,ENNReal.ofReal 4*ENNReal.ofReal (‖raw hell f (t,p)‖^2) ∂energyMeasure μ h) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne
  have he := tendsto_lintegral_of_dominated_convergence (μ := energyMeasure μ h)
    (fun p => ENNReal.ofReal 4*ENNReal.ofReal (‖raw hell f (t,p)‖^2))
    (F := fun n p => ENNReal.ofReal (‖approx hell f n (t,p)-raw hell f (t,p)‖^2))
    (f := fun _ => 0)
    (fun n => ENNReal.continuous_ofReal.measurable.comp (((happrox n).sub hraw).norm.pow_const 2))
    (fun n => Filter.Eventually.of_forall (fun p => by
      change ENNReal.ofReal (‖approx hell f n (t,p)-raw hell f (t,p)‖^2) ≤
        ENNReal.ofReal 4*ENNReal.ofReal (‖raw hell f (t,p)‖^2)
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
      exact ENNReal.ofReal_le_ofReal (approximant_difference_bound
        (t := t) (s := p.1) hell (by exact_mod_cast ht) (f p) n))) hfinite
    (Filter.Eventually.of_forall (fun p => by
      have hs : Tendsto (fun n => approx hell f n (t,p)-raw hell f (t,p)) atTop (𝓝 (0:Columns)) := by
        simpa only [approx,raw,sub_self] using
          (approximant_tendsto (t := t) (s := p.1) hell (by exact_mod_cast ht) (f p)).sub
            (tendsto_const_nhds (x := raw hell f (t,p)))
      have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.norm.pow 2)
      change Tendsto (fun n => ENNReal.ofReal (‖approx hell f n (t,p)-raw hell f (t,p)‖^2))
        atTop (𝓝 (ENNReal.ofReal (‖(0:Columns)‖^2))) at hn
      simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),ENNReal.ofReal_zero] using hn))
  unfold error
  simpa only [lintegral_zero] using he

variable (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)

/-- Every positive fixed-time cell approximation converges in the actual
terminal probability L² space to the literal stopped heat integral. -/
theorem integral_tendsto (t : ℝ≥0) (ht : 0 < t) (hth : t ≤ h) :
    Tendsto (fun n => I.integral (HaarItoApproximation.input 𝓕 μ h hell hM f hf n (ApproximationCells.index n t)))
      atTop (𝓝 (TerminalHaarConvolution.value 𝓕 μ h hh hell hM f hf I t hth)) := by
  apply KernelEnergyCauchy.tendsto_of_energy_error _ _ (error μ h hell f t)
    (error_tendsto 𝓕 μ h hh hell hM f hf t ht hth)
  intro n
  rw [TerminalHaarConvolution.value,I.difference_energy]
  apply le_of_eq
  have hm : Measurable (fun p => ENNReal.ofReal (‖approx hell f n (t,p)-raw hell f (t,p)‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((((approx_measurable hell (hf.mono (predictable_le_product 𝓕)).measurable n).sub
        (raw_measurable hell (hf.mono (predictable_le_product 𝓕)).measurable)).comp
          (measurable_const.prodMk measurable_id)).norm.pow_const 2)
  change _ = ∫⁻ p,ENNReal.ofReal (‖approx hell f n (t,p)-raw hell f (t,p)‖^2) ∂(timeMeasure h).prod μ
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod (HaarItoApproximation.input_at 𝓕 μ h hell hM f hf n ht hth),
    Measure.ae_ae_of_ae_prod (FixedHaarIntegral.input_ae 𝓕 μ h hh hell hM f hf t hth)] with s hs hs'
  apply lintegral_congr_ae
  filter_upwards [hs,hs'] with ω hω hω'
  rw [hω,hω']
  rfl

end SHE.HaarFixedApproximation
