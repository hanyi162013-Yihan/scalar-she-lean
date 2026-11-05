module

public import SHEStochastic.MatrixFactorCongruence
public import SHEStochastic.MatrixPointHeatInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixPointInputCongruence
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem row (P Q : Profile d)
    (h : P.value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] Q.value)
    (τ : ℝ) (x : HeatCircle) (c : d) :
    MatrixPointHeatRows.row τ P x c=MatrixPointHeatRows.row τ Q x c := by
  simp only [MatrixPointHeatRows.row,MatrixFactorCongruence.factor P Q h]

variable {Ω : Type*} [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1)
    (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (P Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (P p).upper ≤ U) (hQUpper : ∀ p, (Q p).upper ≤ V)
    (hP : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (P z.1).value z.2))
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

/-- Native point inputs are unchanged by an actual product-a.e. change
of the matrix covariance or its arbitrary bounding metadata. -/
theorem input
    (h : ∀ᵐ p ∂energyMeasure μ H,
      (P p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] (Q p).value)
    (t : ℝ≥0) (ht : t ≤ H) (x : HeatCircle) (c : d) :
    MatrixPointHeatInput.input F μ H hH U hU P hUpper hP t ht x c=
      MatrixPointHeatInput.input F μ H hH V hV Q hQUpper hQ t ht x c := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product F)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [MatrixPointHeatInput.input_ae F μ H hH U hU P hUpper hP t ht x c,
    MatrixPointHeatInput.input_ae F μ H hH V hV Q hQUpper hQ t ht x c,h] with p hp hq he
  rw [hp,hq,row (P p) (Q p) he]

end SHEStochastic.MatrixPointInputCongruence
