module

public import SHEStochastic.MatrixPointHeatInput
public import SHEStochastic.MatrixStoppedHeatWindow
public import SHEStochastic.WholeFieldRowCovariance
public import SHE.GaussianStoppedRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixStoppedNativeRows
open MeasureTheory Set SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d] {k : ℕ}
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (Q : Fin k → ℝ≥0 × Ω → Profile d) (hUpper : ∀ i p, (Q i p).upper ≤ U)
    (hQ : ∀ i, @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q i z.1).value z.2))
    (σ T : Fin k → ℝ≥0) (hT : ∀ i, T i ≤ H) (x : Fin k → HeatCircle) (color : Fin k → d)

/-- Original observation stops restrict actual native point inputs;
the original heat targets remain unchanged. -/
def input (i : Fin k) : Process (E := Input (d := d)) F μ H :=
  StoppedItoInputs.stop F μ H (σ i)
    (MatrixPointHeatInput.input F μ H hH U hU (Q i) (hUpper i) (hQ i) (T i) (hT i) (x i) (color i))

def row (ω : Ω) (i : Fin k) (r : ℝ) : Input (d := d) :=
  MatrixStoppedHeatWindow.row (fun j s => Q j (s.toNNReal,ω)) (fun j => (σ j : ℝ))
    (fun j => (T j : ℝ)) x color i r

theorem input_ae (i : Fin k) : input F μ H hH U hU Q hUpper hQ σ T hT x color i =ᵐ[energyMeasure μ H]
    fun p => row Q σ T x color p.2 i (p.1 : ℝ) := by
  filter_upwards [StoppedItoInputs.stop_ae F μ H (σ i)
      (MatrixPointHeatInput.input F μ H hH U hU (Q i) (hUpper i) (hQ i) (T i) (hT i) (x i) (color i)),
    MatrixPointHeatInput.input_ae F μ H hH U hU (Q i) (hUpper i) (hQ i) (T i) (hT i) (x i) (color i)] with p hs hp
  change input F μ H hH U hU Q hUpper hQ σ T hT x color i p=_ at hs
  rw [hs]
  unfold row MatrixStoppedHeatWindow.row MatrixStoppedHeatWindow.age
  by_cases h : (p.1 : ℝ) < (σ i : ℝ)
  · rw [Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) (σ i) from h),hp,if_pos h]
    simp only [Real.toNNReal_coe]
  · rw [Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) (σ i) from h),if_neg h]
    simp only [MatrixPointHeatRows.row,lt_self_iff_false,ite_false]

def rows (v b : ℝ≥0) : Fin k → Process (E := Input (d := d)) F μ H :=
  GaussianStoppedRows.rows F μ H v b (input F μ H hH U hU Q hUpper hQ σ T hT x color)

/-- The finite Ito bracket is the literal full stopped matrix Gram,
including original off-diagonal components and differing row profiles. -/
theorem bracket (v b : ℝ≥0) (hbH : b ≤ H) :
    ∀ᵐ ω ∂μ, ∀ᵐ r : ℝ, r ∈ Ioo (v : ℝ) (b : ℝ) →
      StandardFiniteIto.rowCovariance F μ H (rows F μ H hH U hU Q hUpper hQ σ T hT x color v b) ω r=
        Matrix.gram ℝ (fun i => row Q σ T x color ω i r) := by
  apply WholeFieldRowCovariance.bracket v b hbH _ (fun ω : Ω => ω) (row Q σ T x color)
  filter_upwards [ae_all_iff.mpr (fun i => input_ae F μ H hH U hU Q hUpper hQ σ T hT x color i),
    ae_all_iff.mpr (GaussianStoppedRows.rows_ae F μ H v b (input F μ H hH U hU Q hUpper hQ σ T hT x color))] with p hi hr
  intro i hp
  have hri := hr i
  change rows F μ H hH U hU Q hUpper hQ σ T hT x color v b i p=_ at hri
  rw [hri,if_pos hp,hi i]

end SHEStochastic.MatrixStoppedNativeRows
