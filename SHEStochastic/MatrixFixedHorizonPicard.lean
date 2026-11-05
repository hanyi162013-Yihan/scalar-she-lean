module

public import SHEStochastic.KernelItoWeighted
public import SHEStochastic.CausalKernelWeightedComparison
public import SHEStochastic.PredictableBieleckiFixedPoint
public import SHEStochastic.VectorHeatInitialProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixFixedHorizonPicard
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (G : MatrixNonlinearCoefficient.Coefficient d) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖)

include hL hLip

theorem weighted_bound {γ : ℝ} (hγ : 0 < γ)
    (u v : Process (E := Physical (d := d)) F μ H) :
    ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ)
      (MatrixPredictableConvolution.map hH N G u-MatrixPredictableConvolution.map hH N G v)‖^2) ≤
      ENNReal.ofReal (MatrixNonlinearHeatBounds.constant G L*BieleckiKernel.mass γ)*
        ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) (u-v)‖^2) := by
  let a := MatrixPredictableConvolution.nonlinearField G u
  let b := MatrixPredictableConvolution.nonlinearField G v
  have hi := KernelItoWeighted.difference_isometry (model F μ H hH ((G.bound : ℝ)^2+1) (by positivity))
    (NativeMatrixConvolution.terminalIto N) (-γ) a b
  change ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ)
    (MatrixPredictableConvolution.map hH N G u-MatrixPredictableConvolution.map hH N G v)‖^2)=_ at hi
  rw [show 2*(-γ)=-2*γ by ring] at hi
  have hm : Measurable (fun p => ENNReal.ofReal (Real.exp (-2*γ*(p.1 : ℝ))*
      ‖MatrixHeatKernelModel.raw a p-MatrixHeatKernelModel.raw b p‖^2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((measurable_coe_nnreal_real.comp measurable_fst).const_mul (-2*γ)).exp.mul
        (((raw_measurable a).sub (raw_measurable b)).norm.pow_const 2))
  rw [hi]
  change (∫⁻ p, ENNReal.ofReal (Real.exp (-2*γ*(p.1 : ℝ))*
    ‖MatrixHeatKernelModel.raw a p-MatrixHeatKernelModel.raw b p‖^2)
      ∂HaarKernelL2Approximation.measure μ H) ≤ _
  rw [HaarKernelL2Approximation.triple_lintegral μ H hm]
  have hu := (realization_stronglyMeasurable (energyMeasure μ H) (predictable_le_product F) u).measurable
  have hv := (realization_stronglyMeasurable (energyMeasure μ H) (predictable_le_product F) v).measurable
  have he := CausalKernelWeightedComparison.expected_energy μ H hH
    (fun τ p => MatrixAnalyticKernel.kernel τ (a.value p)-MatrixAnalyticKernel.kernel τ (b.value p))
    (fun p => u p-v p) (hu.sub hv)
    (fun τ hτ p => by rw [MatrixAnalyticKernel.zero hτ,MatrixAnalyticKernel.zero hτ,sub_self])
    (MatrixNonlinearHeatBounds.constant G L) (MatrixNonlinearHeatBounds.constant_nonneg G L)
    (by
      intro τ hτ hτ1 p
      letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      exact MatrixNonlinearHeatBounds.bound G (fun p => u p) (fun p => v p)
        (Lp.stronglyMeasurable u) (Lp.stronglyMeasurable v) hL hLip hτ hτ1 p) hγ
  apply he.trans_eq
  congr 1
  rw [PredictableExponential.energy,show 2*(-γ)=-2*γ by ring]
  have hs := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v))
  apply lintegral_congr_ae
  filter_upwards [hs] with s hs
  apply lintegral_congr_ae
  filter_upwards [hs] with ω hω
  rw [hω]
  rfl

/-- The vector mild fixed point exists uniquely on every prescribed
H≤1. The interval is independent of the coefficient's Lipschitz constant;
only the auxiliary Bielecki weight changes. -/
theorem exists_unique_forced (forcing : Process (E := Physical (d := d)) F μ H) :
    ∃! v : Process (E := Physical (d := d)) F μ H,
      v=forcing+MatrixPredictableConvolution.map hH N G v :=
  PredictableBieleckiFixedPoint.exists_unique _ _ (MatrixNonlinearHeatBounds.constant_nonneg G L)
    (fun γ hγ u v => weighted_bound hH N G hL hLip hγ u v) forcing

theorem exists_unique_heat_mild (u : Physical (d := d)) :
    ∃! v : Process (E := Physical (d := d)) F μ H,
      v=VectorHeatInitialProcess.process F μ H u+MatrixPredictableConvolution.map hH N G v :=
  exists_unique_forced hH N G hL hLip (VectorHeatInitialProcess.process F μ H u)

end SHEStochastic.MatrixFixedHorizonPicard
