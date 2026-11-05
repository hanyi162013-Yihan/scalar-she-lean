module

public import SHE.HaarCellIntegrands
public import SHE.PredictableItoCells

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarItoApproximation
open MeasureTheory Set PredictableL2 ApproximationCells HaarKernelApproximation
open scoped NNReal ENNReal
local instance haarItoApproximation_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance haarItoApproximation_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance haarItoApproximation_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance haarItoApproximation_stateSigma : MeasurableSpace LowBands.StateL2 := borel LowBands.StateL2
local instance haarItoApproximation_stateBorel : BorelSpace LowBands.StateL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
variable (hf : StronglyMeasurable[𝓕.predictable] f)

def input (n k : ℕ) : Process (E := Columns) 𝓕 μ h :=
  if hk : k ≠ 0 then HaarCellIntegrands.process 𝓕 μ h hell hM f hf n k hk else 0

theorem input_ae (n k : ℕ) (hk : k ≠ 0) :
    input 𝓕 μ h hell hM f hf n k =ᵐ[energyMeasure μ h] HaarCellIntegrands.kernel hell f n k := by
  simp only [input,dite_eq_left hk]
  exact HaarCellIntegrands.process_ae 𝓕 μ h hell hM f hf n k hk

theorem input_stopped (n k : ℕ) :
    ∀ᵐ p ∂energyMeasure μ h,point n (k-1) < p.1 → input 𝓕 μ h hell hM f hf n k p=0 := by
  by_cases hk : k ≠ 0
  · filter_upwards [input_ae 𝓕 μ h hell hM f hf n k hk] with p hp hs
    rw [hp,HaarCellIntegrands.kernel,ite_eq_right (not_le.mpr hs)]
  · simp only [input,dite_eq_right hk]
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero Columns 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)))] with p hp
    exact fun _ => hp

/-- A genuine finite predictable approximation built from the actual heat
columns and ordinary terminal stochastic integration. -/
def output (I : StandardTerminalIto (C := Columns) (E := LowBands.StateL2) 𝓕 μ h)
    (n : ℕ) : Process (E := LowBands.StateL2) 𝓕 μ h :=
  PredictableItoCells.output I n (input 𝓕 μ h hell hM f hf n)
    (input_stopped 𝓕 μ h hell hM f hf n)

theorem input_at (n : ℕ) {t : ℝ≥0} (ht : 0 < t) (htH : t ≤ h) :
    input 𝓕 μ h hell hM f hf n (index n t) =ᵐ[energyMeasure μ h]
      (fun p => HaarKernelL2Approximation.approx hell f n (t,p)) := by
  have hk : index n t ≠ 0 := by have := (Finset.mem_Icc.mp (index_mem n ht htH)).1; omega
  filter_upwards [input_ae 𝓕 μ h hell hM f hf n _ hk] with p hp
  rw [hp]
  unfold HaarCellIntegrands.kernel HaarKernelL2Approximation.approx approximant
  rw [right_eq_point,left_eq_point n ht]
  have hc : p.1 ≤ point n (index n t-1) ↔ (p.1:ℝ) ≤ (point n (index n t-1):ℝ) := by exact_mod_cast Iff.rfl
  simp only [hc]

end SHE.HaarItoApproximation
