module

public import SHEStochastic.MatrixPointHeatRows
public import SHEStochastic.CausalKernelInput
public import SHEStochastic.NativeRowRepresentatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPointHeatInput
open MeasureTheory SHE SHE.FiniteHaar SHE.StoppedFourier SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩

theorem row_zero {τ : ℝ} (hτ : τ ≤ 0) (P : Profile d) (x : HeatCircle) (i : d) :
    MatrixPointHeatRows.row τ P x i=0 := by
  simp only [MatrixPointHeatRows.row,if_neg (not_lt.mpr hτ)]

def constant (U : ℝ) : ℝ := (1+heatConstant)*U

theorem constant_nonneg {U : ℝ} (hU : 0 ≤ U) : 0 ≤ constant U := by
  unfold constant
  exact mul_nonneg (by linarith [heatConstant_pos]) hU

theorem row_bound {τ U : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (P : Profile d)
    (hP : P.upper ≤ U) (x : HeatCircle) (i : d) :
    ‖MatrixPointHeatRows.row τ P x i‖^2 ≤ constant U*τ^(-(1/2 : ℝ)) := by
  have hU : 0 ≤ U := P.upper_pos.le.trans hP
  have ht : 1 ≤ τ^(-(1/2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  refine (MatrixPointHeatRows.norm_sq hτ P x i).trans ?_
  have hb := mul_le_mul_of_nonneg_right hP
    (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg hτ.le (-(1/2 : ℝ)))))
  have hu := mul_le_mul_of_nonneg_left ht hU
  unfold constant
  nlinarith only [hb,hu]

variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
local notation "ν" => ((energyMeasure μ H).trim (predictable_le_product F))

include hQ in
theorem predictable (t : ℝ≥0) (x : HeatCircle) (i : d) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω =>
      MatrixPointHeatRows.row ((t : ℝ)-(p.1 : ℝ)) (Q p) x i) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (MatrixPointHeatRows.measurable _
    (measurable_const.sub (PredictableClock.real_time_measurable F))
    (fun _ => x) measurable_const Q hQ i).stronglyMeasurable

include hH hU hUpper hQ in
theorem memLp (t : ℝ≥0) (ht : t ≤ H) (x : HeatCircle) (i : d) :
    @MemLp _ _ F.predictable _ _ (fun p : ℝ≥0 × Ω =>
      MatrixPointHeatRows.row ((t : ℝ)-(p.1 : ℝ)) (Q p) x i) 2 ν := by
  exact CausalKernelInput.memLp F μ H hH
    (fun τ p => MatrixPointHeatRows.row τ (Q p) x i)
    (fun τ hτ p => row_zero hτ (Q p) x i) (constant U) (constant_nonneg hU)
    (fun τ hτ hτ1 p => row_bound hτ hτ1 (Q p) (hUpper p) x i)
    t ht (predictable F Q hQ t x i)

/-- The genuine square-integrable native input for a vector point heat
observation; its integrability follows from the proved heat-row bound. -/
def input (t : ℝ≥0) (ht : t ≤ H) (x : HeatCircle) (i : d) : Process (E := Input (d := d)) F μ H :=
  (memLp F μ H hH U hU Q hUpper hQ t ht x i).toLp _

theorem input_ae (t : ℝ≥0) (ht : t ≤ H) (x : HeatCircle) (i : d) :
    input F μ H hH U hU Q hUpper hQ t ht x i =ᵐ[energyMeasure μ H]
      fun p : ℝ≥0 × Ω => MatrixPointHeatRows.row ((t : ℝ)-(p.1 : ℝ)) (Q p) x i :=
  ae_eq_of_ae_eq_trim (memLp F μ H hH U hU Q hUpper hQ t ht x i).coeFn_toLp

def source (t : ℝ≥0) (ht : t ≤ H) (x : HeatCircle) (i : d) :
    Lp (Input (d := d)) 2 (FiniteScalarIto.inputMeasure F μ H) :=
  FiniteCylindricalIto.processTransport (input F μ H hH U hU Q hUpper hQ t ht x i)

theorem source_ae (t : ℝ≥0) (ht : t ≤ H) (x : HeatCircle) (i : d) :
    source F μ H hH U hU Q hUpper hQ t ht x i =ᵐ[FiniteScalarIto.inputMeasure F μ H]
      fun p : ℝ≥0 × Ω => MatrixPointHeatRows.row ((t : ℝ)-(p.1 : ℝ)) (Q p) x i :=
  NativeRowRepresentatives.transport_ae _ _ (predictable F Q hQ t x i)
    (input_ae F μ H hH U hU Q hUpper hQ t ht x i)

end SHEStochastic.MatrixPointHeatInput
