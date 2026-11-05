module

public import SHEStochastic.MatrixPredictableConvolution
public import SHEStochastic.MatrixNonlinearHeatBounds
public import SHEStochastic.CausalKernelComparison
public import SHE.CompanionPicard

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixConstructedPicard
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

/-- The native nonlinear matrix convolution has the same square-root
short-time energy gain as its scalar counterpart. -/
theorem difference_energy (u v : Process (E := Physical (d := d)) F μ H) :
    ENNReal.ofReal (‖MatrixPredictableConvolution.map hH N G u-
      MatrixPredictableConvolution.map hH N G v‖^2) ≤
      ENNReal.ofReal (2*MatrixNonlinearHeatBounds.constant G L*(H : ℝ)^(1/2 : ℝ))*
        ENNReal.ofReal (‖u-v‖^2) := by
  let a := MatrixPredictableConvolution.nonlinearField G u
  let b := MatrixPredictableConvolution.nonlinearField G v
  have hm : Measurable (fun p => ENNReal.ofReal (‖MatrixHeatKernelModel.raw a p-
      MatrixHeatKernelModel.raw b p‖^2)) := ENNReal.continuous_ofReal.measurable.comp
    (((MatrixHeatKernelModel.raw_measurable a).sub (MatrixHeatKernelModel.raw_measurable b)).norm.pow_const 2)
  rw [MatrixPredictableConvolution.map_difference_isometry,
    HaarKernelL2Approximation.triple_lintegral μ H hm,
    process_difference_lintegral_energy F μ H]
  have hu := (realization_stronglyMeasurable (energyMeasure μ H) (predictable_le_product F) u).measurable
  have hv := (realization_stronglyMeasurable (energyMeasure μ H) (predictable_le_product F) v).measurable
  apply CausalKernelComparison.expected_energy μ H hH
    (fun τ p => MatrixAnalyticKernel.kernel τ (a.value p)-MatrixAnalyticKernel.kernel τ (b.value p))
    (fun p => u p-v p) (hu.sub hv)
    (fun τ hτ p => by rw [MatrixAnalyticKernel.zero hτ,MatrixAnalyticKernel.zero hτ,sub_self])
    (MatrixNonlinearHeatBounds.constant G L) (MatrixNonlinearHeatBounds.constant_nonneg G L)
  intro τ hτ hτ1 p
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MatrixNonlinearHeatBounds.bound G (fun p => u p) (fun p => v p)
    (Lp.stronglyMeasurable u) (Lp.stronglyMeasurable v) hL hLip hτ hτ1 p

theorem convolution_lipschitz
    (hsmall : 2*MatrixNonlinearHeatBounds.constant G L*(H : ℝ)^(1/2 : ℝ) ≤ 1/4) :
    LipschitzWith (1/2) (MatrixPredictableConvolution.map hH N G) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he := difference_energy hH N G hL hLip u v
  have hC : 0 ≤ 2*MatrixNonlinearHeatBounds.constant G L*(H : ℝ)^(1/2 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (MatrixNonlinearHeatBounds.constant_nonneg G L))
      (Real.rpow_nonneg H.2 _)
  rw [← ENNReal.ofReal_mul hC] at he
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg ‖u-v‖))).mp he
  have hs := hr.trans (mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u-v‖))
  rw [dist_eq_norm,dist_eq_norm]
  change ‖MatrixPredictableConvolution.map hH N G u-MatrixPredictableConvolution.map hH N G v‖ ≤
    (1/2 : ℝ)*‖u-v‖
  nlinarith [norm_nonneg (MatrixPredictableConvolution.map hH N G u-
    MatrixPredictableConvolution.map hH N G v),norm_nonneg (u-v)]

/-- Actual short-time forced matrix Haar mild solutions are constructed
in the complete predictable L2 process space. The only driving input is
the native Brownian family; no stochastic convolution is assumed. -/
theorem exists_unique_forced
    (hsmall : 2*MatrixNonlinearHeatBounds.constant G L*(H : ℝ)^(1/2 : ℝ) ≤ 1/4)
    (forcing : Process (E := Physical (d := d)) F μ H) :
    ∃! v : Process (E := Physical (d := d)) F μ H,
      v=forcing+MatrixPredictableConvolution.map hH N G v := by
  let Φ := fun v => forcing+MatrixPredictableConvolution.map hH N G v
  have hN := convolution_lipschitz hH N G hL hLip hsmall
  have hΦ : LipschitzWith (1/2) Φ := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [Φ,dist_add_left] using hN.dist_le_mul u v
  have hc : ContractingWith (1/2) Φ := ⟨by norm_num,hΦ⟩
  exact ⟨hc.fixedPoint Φ,hc.fixedPoint_isFixedPt.symm,fun v hv => hc.fixedPoint_unique hv.symm⟩

/-- A positive construction horizon is chosen from the proved matrix
heat estimate before selecting any noise realization or forcing. -/
theorem exists_horizon : ∃ r : ℝ≥0, ∃ hr1 : (r : ℝ) ≤ 1, 0 < r ∧
    ∀ (N : FiniteScalarIto.Family F μ r (d × HaarNode))
      (forcing : Process (E := Physical (d := d)) F μ r),
      ∃! v : Process (E := Physical (d := d)) F μ r,
        v=forcing+MatrixPredictableConvolution.map hr1 N G v := by
  obtain ⟨r,hr,hr1,hs⟩ := CompanionPicard.exists_contraction_horizon
    (MatrixNonlinearHeatBounds.constant_nonneg G L)
  exact ⟨r,hr1,hr,fun N forcing => exists_unique_forced hr1 N G hL hLip hs forcing⟩

end SHEStochastic.MatrixConstructedPicard
