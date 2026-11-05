module

public import SHEStochastic.MatrixUnboundedFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.MatrixUnboundedFourierInputLocality
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (G : EuclideanSpace ℝ d → Matrix d d ℝ)
  {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
  (U V : ℝ≥0×Ω → Physical (d := d))
  (hU : StronglyMeasurable[F.predictable] U)
  (hV : StronglyMeasurable[F.predictable] V)
  (hEU : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))
  (hEV : Integrable (fun p => ‖V p‖^2) (energyMeasure μ H))
  (τ : Ω → WithTop ℝ≥0)
  (hUV : ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 → U p=V p)

include hUV in
/-- Pointwise locality of the literal unbounded Fourier noise row. -/
theorem input (i : d) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ p ∂energyMeasure μ H, (p.1 : WithTop ℝ≥0)<τ p.2 →
      MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 U hU hEU i a m p =
      MatrixUnboundedFourierInput.input F μ H G hG hβ hβ1 V hV hEV i a m p := by
  filter_upwards [hUV,
    MatrixUnboundedFourierInput.input_ae F μ H G hG hβ hβ1 U hU hEU i a m,
    MatrixUnboundedFourierInput.input_ae F μ H G hG hβ hβ1 V hV hEV i a m]
    with p hp hu hv ht
  rw [hu,hv]
  simp only [MatrixUnboundedFourierInput.row,hp ht]

end SHEStochastic.MatrixUnboundedFourierInputLocality
