module

public import SHE.DampedCellIntegrands
public import SHE.KernelItoLimit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.DampedKernelModel
open MeasureTheory Set Filter PredictableL2 ApproximationCells HaarKernelApproximation
open scoped NNReal ENNReal Topology
local instance dampedKernelModel_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance dampedKernelModel_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance dampedKernelModel_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance dampedKernelModel_columnsSigma : MeasurableSpace Columns := borel Columns
local instance dampedKernelModel_columnsBorel : BorelSpace Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

def raw {Λ ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (p : ℝ≥0 × (ℝ≥0 × Ω)) : Columns :=
  DampedHeatKernel.kernel Λ ell M hell ((p.1:ℝ)-(p.2.1:ℝ),f p.2)

def approx {Λ ell M : ℝ} (hell : 0 < ell) (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (n : ℕ) (p : ℝ≥0 × (ℝ≥0 × Ω)) : Columns :=
  DampedHeatKernel.approximant Λ ell M hell n p.1 p.2.1 (f p.2)

theorem raw_measurable {Λ ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M}
    (hf : Measurable f) : Measurable (raw (Λ := Λ) hell f) :=
  (DampedHeatKernel.kernel_measurable Λ ell M hell).comp
    (((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_coe_nnreal_real.comp measurable_snd.fst)).prodMk (hf.comp measurable_snd))

theorem approx_measurable {Λ ell M : ℝ} (hell : 0 < ell) {f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M}
    (hf : Measurable f) (n : ℕ) : Measurable (approx (Λ := Λ) hell f n) := by
  change Measurable (fun p : ℝ≥0 × (ℝ≥0 × Ω) =>
    Real.exp (-Λ*(ApproximationClock.right n (p.1:ℝ)-(p.2.1:ℝ))) •
      HaarKernelL2Approximation.approx hell f n p)
  have he : Measurable (fun p : ℝ≥0 × (ℝ≥0 × Ω) =>
      Real.exp (-Λ*(ApproximationClock.right n (p.1:ℝ)-(p.2.1:ℝ)))) :=
    Real.measurable_exp.comp (measurable_const.mul
      (((ApproximationClock.right_measurable n).comp
        (measurable_coe_nnreal_real.comp measurable_fst)).sub
          (measurable_coe_nnreal_real.comp measurable_snd.fst)))
  exact he.smul (HaarKernelL2Approximation.approx_measurable hell hf n)

theorem raw_energy_finite {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M} (hf : Measurable f) :
    (∫⁻ p,ENNReal.ofReal (‖raw (Λ := Λ) hell f p‖^2) ∂HaarKernelL2Approximation.measure μ h) < ∞ := by
  have hb : (∫⁻ p,ENNReal.ofReal (‖raw (Λ := Λ) hell f p‖^2) ∂HaarKernelL2Approximation.measure μ h) ≤
      ∫⁻ p,ENNReal.ofReal (‖HaarKernelL2Approximation.raw hell f p‖^2) ∂HaarKernelL2Approximation.measure μ h := by
    apply lintegral_mono
    intro p
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
      (DampedHeatKernel.kernel_norm_le (t := (p.1:ℝ)-(p.2.1:ℝ)) hΛ hell (f p.2)) 2)
  exact hb.trans_lt (HaarKernelL2Approximation.raw_energy_finite hell hM μ h hh hf)

theorem input_at (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (n : ℕ) {t : ℝ≥0} (ht : 0 < t) (htH : t ≤ h) :
    DampedCellIntegrands.input 𝓕 μ h hΛ hell hM f hf n (index n t) =ᵐ[energyMeasure μ h]
      (fun p => approx (Λ := Λ) hell f n (t,p)) := by
  have hk : index n t ≠ 0 := by have := (Finset.mem_Icc.mp (index_mem n ht htH)).1; omega
  filter_upwards [DampedCellIntegrands.input_ae 𝓕 μ h hΛ hell hM f hf n _ hk] with p hp
  rw [hp]
  unfold DampedCellIntegrands.kernel approx DampedHeatKernel.approximant
    HaarCellIntegrands.kernel HaarKernelApproximation.approximant
  rw [right_eq_point,left_eq_point n ht]
  have hc : p.1 ≤ point n (index n t-1) ↔ (p.1:ℝ) ≤ (point n (index n t-1):ℝ) := by exact_mod_cast Iff.rfl
  simp only [hc]

def Fields (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (ell M : ℝ) :=
  {f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M // StronglyMeasurable[𝓕.predictable] f}

/-- Every condition of the generic finite-cell closure is proved for the
literal exponentially damped common-Haar kernel. -/
def model (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
    {Λ ell M : ℝ} (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M) :
    KernelItoLimit.Model (Fields 𝓕 ell M) Columns 𝓕 μ h where
  raw a := raw (Λ := Λ) hell a.1
  approx a := approx (Λ := Λ) hell a.1
  raw_measurable a := raw_measurable hell (a.2.mono (predictable_le_product 𝓕)).measurable
  approx_measurable a n := approx_measurable hell (a.2.mono (predictable_le_product 𝓕)).measurable n
  raw_energy_finite a := raw_energy_finite hΛ hell hM μ h hh (a.2.mono (predictable_le_product 𝓕)).measurable
  approx_tendsto a := (Measure.quasiMeasurePreserving_fst.ae
    ((timeMeasure_ae_mem h).mono (fun _ ht => ht.1))).mono (fun p hp =>
      DampedHeatKernel.approximant_tendsto (t := p.1) (s := p.2.1) hell (by exact_mod_cast hp) (a.1 p.2))
  approx_norm_le a n := (Measure.quasiMeasurePreserving_fst.ae
    ((timeMeasure_ae_mem h).mono (fun _ ht => ht.1))).mono (fun p hp =>
      DampedHeatKernel.approximant_norm_le (t := p.1) (s := p.2.1) hΛ hell (by exact_mod_cast hp) (a.1 p.2) n)
  input a := DampedCellIntegrands.input 𝓕 μ h hΛ hell hM a.1 a.2
  input_stopped a := DampedCellIntegrands.input_stopped 𝓕 μ h hΛ hell hM a.1 a.2
  input_at a n t ht htH := input_at 𝓕 μ h hΛ hell hM a.1 a.2 n ht htH

end SHE.DampedKernelModel
