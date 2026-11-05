module

public import SHEStochastic.MatrixFourierInput
public import SHEStochastic.HolderCoefficientEnergyGrowth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedFourierInput
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
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (hEnergy : Integrable (fun p => ‖U p‖^2) (energyMeasure μ H))
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
local instance : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure;infer_instance

/-- The original, possibly unbounded, matrix coefficient against a Fourier test. -/
def row (p : ℝ≥0×Ω) : Input (d := d) :=
  FourierHeatInput.multiplier H n p • VectorWhiteCoordinates.analysis
    (StateNoiseCovariance.row ν hβ hβ1 (MatrixDiffusionRows.holder hG i) (weight a n) (U p))

include hU in
theorem predictable : StronglyMeasurable[F.predictable] (row H G hG hβ hβ1 U i a n) :=
  (FourierHeatInput.multiplier_measurable F H n).smul
    ((VectorWhiteCoordinates.analysis (d := d)).continuous.comp_stronglyMeasurable
      ((StateNoiseCovariance.row_continuous ν hβ hβ1 (MatrixDiffusionRows.holder hG i)
        (weight a n)).comp_stronglyMeasurable hU))

def energyConstant : ℝ :=
  Real.exp ((H : ℝ)*(n : ℝ)^2)^2 *
    (‖weight a n‖^2*(4*(‖MatrixDiffusionRows.row i (G 0)‖+(C : ℝ))^2))

theorem energyConstant_nonneg : 0 ≤ energyConstant H G (C := C) i a n := by
  unfold energyConstant
  positivity

theorem norm_sq_bound (p : ℝ≥0×Ω) :
    ‖row H G hG hβ hβ1 U i a n p‖^2 ≤
      energyConstant H G (C := C) i a n*(1+‖U p‖^2) := by
  rw [row,norm_smul,Real.norm_eq_abs,LinearIsometryEquiv.norm_map,mul_pow]
  have he := pow_le_pow_left₀ (abs_nonneg _) (FourierHeatInput.multiplier_bound H n p) 2
  have hr := HolderCoefficientEnergyGrowth.row_bound ν (MatrixDiffusionRows.holder hG i)
    hβ hβ1 (weight a n) (U p)
  exact (mul_le_mul he hr (sq_nonneg _) (sq_nonneg _)).trans_eq (by
    unfold energyConstant
    ring)

include hU hEnergy in
theorem memLp_product : MemLp (row H G hG hβ hβ1 U i a n) 2 (energyMeasure μ H) := by
  have hm := (predictable F H G hG hβ hβ1 U hU i a n).mono (predictable_le_product F)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact (((integrable_const (1 : ℝ)).add hEnergy).const_mul
    (energyConstant H G (C := C) i a n)).mono'
      (hm.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        change ‖‖row H G hG hβ hβ1 U i a n p‖^2‖ ≤ _
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact norm_sq_bound H G hG hβ hβ1 U i a n p)

include hU hEnergy in
theorem memLp_trim : MemLp (row H G hG hβ hβ1 U i a n) 2
    ((energyMeasure μ H).trim (predictable_le_product F)) := by
  rw [MemLp,eLpNorm_trim (predictable_le_product F) (predictable F H G hG hβ hβ1 U hU i a n)]
  exact memLp_product F μ H G hG hβ hβ1 U hU hEnergy i a n

def input : Process (E := Input (d := d)) F μ H := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact (memLp_trim F μ H G hG hβ hβ1 U hU hEnergy i a n).toLp _

theorem input_ae_trim : input F μ H G hG hβ hβ1 U hU hEnergy i a n
    =ᵐ[(energyMeasure μ H).trim (predictable_le_product F)] row H G hG hβ hβ1 U i a n := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  exact (memLp_trim F μ H G hG hβ hβ1 U hU hEnergy i a n).coeFn_toLp

theorem input_ae : input F μ H G hG hβ hβ1 U hU hEnergy i a n =ᵐ[energyMeasure μ H]
    row H G hG hβ hβ1 U i a n :=
  ae_eq_of_ae_eq_trim (input_ae_trim F μ H G hG hβ hβ1 U hU hEnergy i a n)

end SHEStochastic.MatrixUnboundedFourierInput
