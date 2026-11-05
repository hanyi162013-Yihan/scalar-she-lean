module

public import SHE.HaarItoApproximation
public import SHE.PredictableItoEnergy
public import SHE.KernelEnergyMeasure
public import SHE.KernelEnergyCauchy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarItoApproximation
open MeasureTheory Set Filter PredictableL2 ApproximationCells HaarKernelApproximation
open HaarKernelL2Approximation
open scoped NNReal ENNReal Topology
local instance haarItoEnergy_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarItoEnergy_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance haarItoEnergy_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance haarItoEnergy_columnsSigma : MeasurableSpace Columns := borel Columns
local instance haarItoEnergy_columnsBorel : BorelSpace Columns := ⟨rfl⟩
local instance haarItoEnergy_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarItoEnergy_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)
variable (f g : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
variable (hf : StronglyMeasurable[𝓕.predictable] f) (hg : StronglyMeasurable[𝓕.predictable] g)

theorem output_pair_energy (n m : ℕ) :
    ENNReal.ofReal (‖output 𝓕 μ h hell hM f hf I n-output 𝓕 μ h hell hM g hg I m‖^2)=
      ∫⁻ p,ENNReal.ofReal (‖approx hell f n p-approx hell g m p‖^2) ∂measure μ h := by
  have hfm := (hf.mono (predictable_le_product 𝓕)).measurable
  have hgm := (hg.mono (predictable_le_product 𝓕)).measurable
  have hm : Measurable (fun p => ENNReal.ofReal (‖approx hell f n p-approx hell g m p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((approx_measurable hell hfm n).sub (approx_measurable hell hgm m)).norm.pow_const 2)
  rw [output,output,PredictableItoCells.output_difference_energy,triple_lintegral μ h hm]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  have hfn := Measure.ae_ae_of_ae_prod (input_at 𝓕 μ h hell hM f hf n ht.1 ht.2)
  have hgn := Measure.ae_ae_of_ae_prod (input_at 𝓕 μ h hell hM g hg m ht.1 ht.2)
  apply lintegral_congr_ae
  filter_upwards [hfn,hgn] with s hs hs'
  apply lintegral_congr_ae
  filter_upwards [hs,hs'] with ω hω hω'
  rw [hω,hω']

def error (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p,ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2) ∂measure μ h

theorem output_difference_bound (n m : ℕ) :
    ENNReal.ofReal (‖output 𝓕 μ h hell hM f hf I n-output 𝓕 μ h hell hM f hf I m‖^2) ≤
      2*error μ h hell f n+2*error μ h hell f m := by
  have hfm := (hf.mono (predictable_le_product 𝓕)).measurable
  have he (n : ℕ) : Measurable (fun p => ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((approx_measurable hell hfm n).sub (raw_measurable hell hfm)).norm.pow_const 2)
  rw [output_pair_energy 𝓕 μ h hell hM I f f hf hf]
  calc
    _ ≤ ∫⁻ p,(2:ℝ≥0∞)*ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2)+
        2*ENNReal.ofReal (‖approx hell f m p-raw hell f p‖^2) ∂measure μ h := by
      apply lintegral_mono
      intro p
      have hn := norm_nonneg (approx hell f n p-raw hell f p)
      have hm := norm_nonneg (approx hell f m p-raw hell f p)
      have htriangle : ‖approx hell f n p-approx hell f m p‖ ≤
          ‖approx hell f n p-raw hell f p‖+‖approx hell f m p-raw hell f p‖ := by
        simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub
          (approx hell f n p) (raw hell f p) (approx hell f m p)
      have hsq : ‖approx hell f n p-approx hell f m p‖^2 ≤
          2*‖approx hell f n p-raw hell f p‖^2+2*‖approx hell f m p-raw hell f p‖^2 := by
        nlinarith [norm_nonneg (approx hell f n p-approx hell f m p),sq_nonneg
          (‖approx hell f n p-raw hell f p‖-‖approx hell f m p-raw hell f p‖)]
      have hb := ENNReal.ofReal_le_ofReal hsq
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)] at hb
      simpa only [ENNReal.ofReal_ofNat] using hb
    _ = _ := by
      have h2n : Measurable (fun p => (2:ℝ≥0∞)*ENNReal.ofReal (‖approx hell f n p-raw hell f p‖^2)) :=
        measurable_const.mul (he n)
      rw [lintegral_add_left h2n,
        lintegral_const_mul' _ _ (by norm_num),lintegral_const_mul' _ _ (by norm_num)]
      rfl

theorem output_cauchy (hh : (h:ℝ) ≤ 1) :
    CauchySeq (output 𝓕 μ h hell hM f hf I) := by
  apply KernelEnergyCauchy.cauchy_of_energy_error _ (error μ h hell f)
  · exact approximation_energy_tendsto hell hM μ h hh
      (hf.mono (predictable_le_product 𝓕)).measurable
  · exact output_difference_bound 𝓕 μ h hell hM I f hf

end SHE.HaarItoApproximation
