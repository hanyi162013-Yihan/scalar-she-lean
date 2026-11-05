module

public import SHEStochastic.MatrixRandomMildExistence
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.MatrixRandomInitialLaw
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (G : MatrixNonlinearCoefficient.Coefficient d) (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (Z : Ω → Physical (d := d))

theorem initial (he : MatrixRandomMildExistence.Equation G hH N U hU Z) :
    (fun ω => U (0,ω)) =ᵐ[μ] Z := by
  let a := MatrixContinuousMild.field G U hU
  have hi : MatrixAnalyticConvolution.input F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) a.value a.upper a.measurable 0 (show 0 ≤ H from zero_le) = 0 := by
    apply NativeInputPairing.process_ext
    have hz : (0 : Process (E := MatrixHaarKernel.Columns (d := d)) F μ H) =ᵐ[energyMeasure μ H]
        (fun _ => (0 : MatrixHaarKernel.Columns (d := d))) :=
      ae_eq_of_ae_eq_trim (Lp.coeFn_zero (MatrixHaarKernel.Columns (d := d)) 2
        ((energyMeasure μ H).trim (predictable_le_product F)))
    filter_upwards [hz,MatrixAnalyticConvolution.input_ae F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) a.value a.upper a.measurable 0 (show 0 ≤ H from zero_le)] with p hz hp
    rw [hp,hz,MatrixAnalyticKernel.zero (by simp)]
  have hv : MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) a.value a.upper a.measurable N 0 (show 0 ≤ H from zero_le) = 0 := by
    unfold MatrixAnalyticConvolution.value
    rw [hi,map_zero]
  have he₀ := he 0 (show 0 ≤ H from zero_le)
  change (fun ω => U (0,ω)) =ᵐ[μ] fun ω => VectorAnalyticHeat.heat 0 (Z ω)+
    MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) a.value a.upper a.measurable N 0 (show 0 ≤ H from zero_le) ω at he₀
  rw [hv] at he₀
  have hz : ∀ᵐ ω ∂μ, (0 : Lp (Physical (d := d)) 2 μ) ω = (0 : Physical (d := d)) := by
    simpa using (Lp.coeFn_zero (Physical (d := d)) 2 μ)
  filter_upwards [he₀,hz] with ω heω hzω
  simpa only [VectorAnalyticHeat.zero,ContinuousLinearMap.id_apply,hzω,add_zero] using heω

/-- Every constructed random approximation has precisely the given initial law. -/
theorem law (he : MatrixRandomMildExistence.Equation G hH N U hU Z) :
    μ.map (fun ω => U (0,ω)) = μ.map Z := Measure.map_congr (initial G hH N U hU Z he)

end SHEStochastic.MatrixRandomInitialLaw
