module

public import SHE.DisjointNegative
public import SHE.DyadicArcs

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.DyadicLocalization
open Finset Set MeasureTheory AddCircle CircleHeat FiniteHaar ArcFourier ArcNegative
local instance dyadicLocalization_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem negativeSq_eq_negativeEnergy (Λ ρ : ℝ) (f : CircleL2) :
    negativeSq Λ ρ f = StepInput.negativeEnergy 1 Λ ρ f := by
  unfold negativeSq StepInput.negativeEnergy weightedFourierSq massiveWeight weight
  simp only [one_mul]

/-- The manuscript's negative disjoint-localization inequality for the
literal dyadic cells and actual circle L² restriction operators, with
a single constant uniform over every depth and every Λ ≥ 1. -/
theorem exists_cell_localization_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (n : ℕ) (f : CircleL2),
      (∑ x : Grid n, StepInput.negativeEnergy 1 Λ ρ (cellRestriction n x f)) ≤
        C*StepInput.negativeEnergy 1 Λ ρ f := by
  obtain ⟨C,hC,hbound⟩ := DisjointNegative.exists_negative_localization_bound hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro Λ hΛ n f
  have hd (x z : Grid n) (hxz : x ≠ z) : Disjoint
      (ArcGeometry.arcSet ((gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ)) (((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ)))
      (ArcGeometry.arcSet ((gridOrdinal n z:ℝ)/((2^n:ℕ):ℝ)) (((gridOrdinal n z:ℝ)+1)/((2^n:ℕ):ℝ))) := by
    rw [← DyadicArcs.cellSet_eq_arcSet,← DyadicArcs.cellSet_eq_arcSet]
    exact cellSet_disjoint n x z hxz
  have hh := hbound (Grid n) Λ hΛ
    (fun x => ((gridOrdinal n x:ℝ)/((2^n:ℕ):ℝ)))
    (fun x => (((gridOrdinal n x:ℝ)+1)/((2^n:ℕ):ℝ))) hd f
  simpa only [← DyadicArcs.cellRestriction_eq_arcRestriction,negativeSq_eq_negativeEnergy] using hh

theorem cellIndicator_positive {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) :
    Summable (fun k : ℤ => weight Λ ρ k*‖fourierCoeff (cellIndicator n x) k‖^2) ∧
      positiveSq Λ ρ (cellIndicator n x) ≤
        inverseConstant 1 ρ*(Λ+(((2^n:ℕ):ℝ))^2)^ρ*(((2^n:ℕ):ℝ))⁻¹ := by
  have hs := summable_stepLp_massive (2^n) (fun j => (Pi.single x 1 : Grid n → ℝ) ((gridCellEquiv n).symm j)) zero_le_one hΛ hρ hρhalf
  have hb := stepLp_massive_inverse (2^n) (fun j => (Pi.single x 1 : Grid n → ℝ) ((gridCellEquiv n).symm j)) zero_le_one hΛ hρ hρhalf
  change Summable _ ∧ _
  have he : stepLp (2^n) (fun j => (Pi.single x 1 : Grid n → ℝ) ((gridCellEquiv n).symm j)) = cellIndicator n x := rfl
  rw [he,cellIndicator_norm_sq] at hb
  rw [he] at hs
  simpa only [positiveSq,weight,massiveWeight,weightedFourierSq,one_mul] using And.intro hs hb

end SHE.DyadicLocalization
