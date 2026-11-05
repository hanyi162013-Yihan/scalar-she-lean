module

public import SHEStochastic.MatrixHeatCellInput
public import SHEStochastic.CausalKernelInput
public import SHE.KernelItoLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixHeatKernelModel
open MeasureTheory Set Filter SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixAnalyticKernel
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩

/-- Predictable spatial matrix profiles, with one deterministic upper
ellipticity bound. The lower bound is already part of each actual profile. -/
structure Fields (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (U : ℝ) where
  value : ℝ≥0 × Ω → Profile d
  upper : ∀ p, (value p).upper ≤ U
  measurable : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (value z.1).value z.2)

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {U : ℝ}

theorem Fields.ambient_measurable (a : Fields (d := d) F U) :
    Measurable (fun z : (ℝ≥0 × Ω) × AddCircle (1 : ℝ) => (a.value z.1).value z.2) :=
  a.measurable.comp
    ((measurable_fst.mono le_rfl (predictable_le_product F)).prodMk measurable_snd)

def raw (a : Fields (d := d) F U) (p : ℝ≥0 × (ℝ≥0 × Ω)) : MatrixHaarKernel.Columns (d := d) :=
  kernel ((p.1 : ℝ)-(p.2.1 : ℝ)) (a.value p.2)

def approx (a : Fields (d := d) F U) (n : ℕ) (p : ℝ≥0 × (ℝ≥0 × Ω)) :
    MatrixHaarKernel.Columns (d := d) :=
  MatrixHeatKernelApproximation.approximant n p.1 p.2.1 (a.value p.2)

theorem raw_measurable (a : Fields (d := d) F U) : Measurable (raw a) :=
  MatrixAnalyticKernel.measurable _
    ((measurable_coe_nnreal_real.comp measurable_fst).sub
      (measurable_coe_nnreal_real.comp measurable_snd.fst)) _
    (a.ambient_measurable.comp (measurable_fst.snd.prodMk measurable_snd))

theorem approx_measurable (a : Fields (d := d) F U) (n : ℕ) : Measurable (approx a n) :=
  MatrixHeatKernelApproximation.measurable _ _
    (measurable_coe_nnreal_real.comp measurable_fst)
    (measurable_coe_nnreal_real.comp measurable_snd.fst) _
    (a.ambient_measurable.comp (measurable_fst.snd.prodMk measurable_snd)) n

theorem raw_energy_finite (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (hH : (H : ℝ) ≤ 1) (hU : 0 ≤ U) (a : Fields (d := d) F U) :
    (∫⁻ p, ENNReal.ofReal (‖raw a p‖^2) ∂HaarKernelL2Approximation.measure μ H) < ∞ := by
  have hm : Measurable (fun p => ENNReal.ofReal (‖raw a p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp ((raw_measurable a).norm.pow_const 2)
  rw [HaarKernelL2Approximation.triple_lintegral μ H hm]
  have hC := constant_nonneg (d := d) hU
  have hb : (∫⁻ t, ∫⁻ s, ∫⁻ ω, ENNReal.ofReal (‖raw a (t,(s,ω))‖^2)
      ∂μ ∂timeMeasure H ∂timeMeasure H) ≤
      ∫⁻ _ : ℝ≥0, ENNReal.ofReal (constant d U*2) ∂timeMeasure H := by
    apply lintegral_mono_ae
    filter_upwards [timeMeasure_ae_mem H] with t ht
    have he := CausalKernelInput.fixed_energy
      (fun τ p => kernel τ (a.value p))
      (fun τ hτ p => MatrixAnalyticKernel.zero hτ (a.value p))
      (constant d U) hC
      (fun τ hτ hτ1 p => (small_bound hτ hτ1 (a.value p)).trans
        (mul_le_mul_of_nonneg_right (constant_mono (a.upper p))
          (Real.rpow_nonneg hτ.le _))) μ hH ht.2
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    have ht1 : (t : ℝ) ≤ 1 := (by exact_mod_cast ht.2 : (t : ℝ) ≤ H).trans hH
    have hp : (t : ℝ)^(1/2 : ℝ) ≤ 1 := by
      exact (Real.rpow_le_rpow t.2 ht1 (by norm_num : (0 : ℝ) ≤ 1/2)).trans_eq
        (Real.one_rpow _)
    exact mul_le_mul_of_nonneg_left (by linarith : 2*(t : ℝ)^(1/2 : ℝ) ≤ 2) hC
  exact hb.trans_lt (by simp only [lintegral_const]; finiteness)

/-- The literal matrix heat kernels satisfy every hypothesis of the
existing predictable finite-cell closure. No stochastic convergence or
adaptedness premise is added to this construction. -/
def model (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U) :
    KernelItoLimit.Model (Fields (d := d) F U) (MatrixHaarKernel.Columns (d := d)) F μ H where
  raw := raw
  approx := approx
  raw_measurable := raw_measurable
  approx_measurable := approx_measurable
  raw_energy_finite a := raw_energy_finite μ H hH hU a
  approx_tendsto a := (Measure.quasiMeasurePreserving_fst.ae
    ((timeMeasure_ae_mem H).mono (fun _ ht => ht.1))).mono (fun p hp =>
      MatrixHeatKernelApproximation.tendsto (t := p.1) (s := p.2.1)
        (by exact_mod_cast hp) (a.value p.2))
  approx_norm_le a n := (Measure.quasiMeasurePreserving_fst.ae
    ((timeMeasure_ae_mem H).mono (fun _ ht => ht.1))).mono (fun p hp =>
      MatrixHeatKernelApproximation.norm_le (t := p.1) (s := p.2.1)
        (by exact_mod_cast hp) (a.value p.2) n)
  input a := MatrixHeatCellInput.input F μ H U hU a.value a.upper a.measurable
  input_stopped a := MatrixHeatCellInput.stopped F μ H U hU a.value a.upper a.measurable
  input_at a n t ht htH := MatrixHeatCellInput.input_at F μ H U hU a.value a.upper a.measurable n ht htH

end SHEStochastic.MatrixHeatKernelModel
