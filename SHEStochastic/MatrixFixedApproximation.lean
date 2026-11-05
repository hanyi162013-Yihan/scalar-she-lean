module

public import SHEStochastic.MatrixPredictableConvolution
public import SHEStochastic.MatrixAnalyticConvolution
public import SHEStochastic.DominatedKernelApproximation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixFixedApproximation
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ) ≤ 1) {U : ℝ} (hU : 0 ≤ U)
    (a : Fields (d := d) F U)

include hH hU

theorem error_tendsto (t : ℝ≥0) (ht : 0 < t) (htH : t ≤ H) :
    Tendsto (fun n => ∫⁻ p, ENNReal.ofReal (‖approx a n (t,p)-raw a (t,p)‖^2)
      ∂energyMeasure μ H) atTop (𝓝 0) := by
  have hm := MatrixAnalyticConvolution.memLp F μ H hH U hU a.value a.upper a.measurable t htH
  have hmem : MemLp (fun p => raw a (t,p)) 2 (energyMeasure μ H) :=
    memLp_of_memLp_trim (predictable_le_product F) hm
  exact DominatedKernelApproximation.energy_tendsto _
    ((raw_measurable a).comp (measurable_const.prodMk measurable_id)) hmem _
    (fun n => (approx_measurable a n).comp (measurable_const.prodMk measurable_id))
    (fun n => Filter.Eventually.of_forall fun p => MatrixHeatKernelApproximation.norm_le
      (by exact_mod_cast ht) (a.value p) n)
    (Filter.Eventually.of_forall fun p => MatrixHeatKernelApproximation.tendsto
      (by exact_mod_cast ht) (a.value p))

/-- At each positive deterministic target, the actual adapted cells
converge to the original native terminal matrix heat integral in L2. -/
theorem integral_tendsto (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (t : ℝ≥0) (ht : 0 < t) (htH : t ≤ H) :
    Tendsto (fun n => (NativeMatrixConvolution.terminalIto N).integral
      (MatrixHeatCellInput.input F μ H U hU a.value a.upper a.measurable n (ApproximationCells.index n t)))
      atTop (𝓝 (MatrixAnalyticConvolution.value F μ H hH U hU a.value a.upper a.measurable N t htH)) := by
  apply KernelEnergyCauchy.tendsto_of_energy_error _ _ _ (error_tendsto (μ := μ) hH hU a t ht htH)
  intro n
  unfold MatrixAnalyticConvolution.value
  rw [(NativeMatrixConvolution.terminalIto N).difference_energy]
  apply le_of_eq
  have hm : Measurable (fun p => ENNReal.ofReal (‖approx a n (t,p)-raw a (t,p)‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((((approx_measurable a n).sub (raw_measurable a)).comp
        (measurable_const.prodMk measurable_id)).norm.pow_const 2)
  change _ = ∫⁻ p, ENNReal.ofReal (‖approx a n (t,p)-raw a (t,p)‖^2) ∂(timeMeasure H).prod μ
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod
    (MatrixHeatCellInput.input_at F μ H U hU a.value a.upper a.measurable n ht htH),
    Measure.ae_ae_of_ae_prod
      (MatrixAnalyticConvolution.input_ae F μ H hH U hU a.value a.upper a.measurable t htH)] with s hs hs'
  apply lintegral_congr_ae
  filter_upwards [hs,hs'] with ω hω hω'
  rw [hω,hω']
  rfl

end SHEStochastic.MatrixFixedApproximation
