module

public import SHEStochastic.MatrixStateNoise
public import SHEStochastic.MatrixFourierCoordinates
public import SHEStochastic.FourierHeatInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFourierInput
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure;infer_instance

def row (p : ℝ≥0×Ω) : Input (d := d) :=
  FourierHeatInput.multiplier H n p • VectorWhiteCoordinates.analysis
    (MatrixStateNoise.row G hG hβ hβ1 i (weight a n) (U p))

include hU in
theorem predictable : StronglyMeasurable[F.predictable] (row H G hG hβ hβ1 U i a n) :=
  (FourierHeatInput.multiplier_measurable F H n).smul
    ((VectorWhiteCoordinates.analysis (d := d)).continuous.comp_stronglyMeasurable
      ((MatrixStateNoise.row_continuous G hG hβ hβ1 i (weight a n)).comp_stronglyMeasurable hU))

def commonCap (B : ℝ≥0) : ℝ≥0 :=
  ⟨Real.exp ((H : ℝ)*(n : ℝ)^2)*‖weight a n‖*(B : ℝ),by positivity⟩

def cap : ℝ≥0 := commonCap H a n G.bound

theorem norm_bound (p : ℝ≥0×Ω) : ‖row H G hG hβ hβ1 U i a n p‖ ≤ cap H G a n := by
  rw [row,norm_smul,Real.norm_eq_abs,LinearIsometryEquiv.norm_map]
  exact (mul_le_mul (FourierHeatInput.multiplier_bound H n p)
    (MatrixStateNoise.row_bound G hG hβ hβ1 i (weight a n) (U p)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by
      change Real.exp ((H : ℝ)*(n : ℝ)^2)*(‖weight a n‖*(G.bound : ℝ))=
        Real.exp ((H : ℝ)*(n : ℝ)^2)*‖weight a n‖*(G.bound : ℝ)
      ring)

def input : Process (E := Input (d := d)) F μ H := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact (MemLp.of_bound (predictable F H G hG hβ hβ1 U hU i a n).aestronglyMeasurable
    (cap H G a n) (Filter.Eventually.of_forall (norm_bound H G hG hβ hβ1 U i a n))).toLp _

theorem input_ae_trim : input F μ H G hG hβ hβ1 U hU i a n =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)]
    row H G hG hβ hβ1 U i a n := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact (MemLp.of_bound (μ := (energyMeasure μ H).trim (predictable_le_product F))
    (predictable F H G hG hβ hβ1 U hU i a n).aestronglyMeasurable (cap H G a n)
      (Filter.Eventually.of_forall (norm_bound H G hG hβ hβ1 U i a n))).coeFn_toLp

theorem input_ae : input F μ H G hG hβ hβ1 U hU i a n =ᵐ[energyMeasure μ H]
    row H G hG hβ hβ1 U i a n := ae_eq_of_ae_eq_trim (input_ae_trim F μ H G hG hβ hβ1 U hU i a n)

theorem input_bound : ∀ᵐ p ∂FiniteScalarIto.inputMeasure F μ H,
    ‖input F μ H G hG hβ hβ1 U hU i a n p‖ ≤ cap H G a n := by
  rw [NativeRowRepresentatives.inputMeasure_eq]
  filter_upwards [input_ae_trim F μ H G hG hβ hβ1 U hU i a n] with p hp
  rw [hp]
  exact norm_bound H G hG hβ hβ1 U i a n p

theorem input_bound_of_le (B : ℝ≥0) (hB : G.bound ≤ B) :
    ∀ᵐ p ∂FiniteScalarIto.inputMeasure F μ H,
      ‖input F μ H G hG hβ hβ1 U hU i a n p‖ ≤ commonCap H a n B := by
  filter_upwards [input_bound F μ H G hG hβ hβ1 U hU i a n] with p hp
  apply hp.trans
  change Real.exp ((H : ℝ)*(n : ℝ)^2)*‖weight a n‖*(G.bound : ℝ) ≤
    Real.exp ((H : ℝ)*(n : ℝ)^2)*‖weight a n‖*(B : ℝ)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (by positivity)

end SHEStochastic.MatrixFourierInput
