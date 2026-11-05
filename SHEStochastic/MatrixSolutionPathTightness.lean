module

public import SHEStochastic.MatrixMildPathRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixSolutionPathTightness
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H)
    (G : ℕ → MatrixNonlinearCoefficient.Coefficient (Fin n))
    (N : ℕ → FiniteScalarIto.Family F μ H ((Fin n) × HaarNode))
    (U : ℕ → ℝ≥0 × Ω → Physical (d := Fin n))
    (hU : ∀ m, StronglyMeasurable[F.predictable] (U m))
    (hc : ∀ m ω, Continuous (fun t => U m (t,ω)))
    (u₀ : Physical (d := Fin n))

include hH0 in
/-- Uniform covariance bounds give tight laws of the actual coupled
vector mild solutions. No compactness of their laws is an input. -/
theorem tight_random (Z : Ω → Physical (d := Fin n)) (hZ : Measurable Z) (cap : ℝ) (hcap : 0 ≤ cap) (hCaps : ∀ m, NativeMatrixEquation.cap (G m) ≤ cap)
    (hEq : ∀ m, MatrixRandomMildExistence.Equation (G m) hH (N m) (U m) (hU m) Z) :
    IsTightMeasureSet (Set.range (fun m => μ.map
      (NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hc m)))) := by
  obtain ⟨Y,hYm,hYrep,_,hYtight⟩ := MatrixPointFieldTightness.exists_tight_versions
    F μ H cap hcap hH
    (fun m => NativeMatrixEquation.profile F (G m) (U m) (hU m))
    (fun m p => hCaps m)
    (fun m => NativeMatrixEquation.profile_measurable F (G m) (U m) (hU m)) N
  have he (m : ℕ) : NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hc m) =ᵐ[μ]
      fun ω => VectorMildPathTightness.path H hH0 (Z ω) (Y m ω) := by
    apply MatrixMildPathRecognition.path_eq_random (G m) hH (N m) (U m) (hU m)
      hH0 (Y m) (hYm m) _ Z hZ (hEq m) (hc m)
    intro p i
    exact hYrep i m p
  have hm (m : ℕ) : μ.map (NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hc m)) =
      μ.map (fun ω => VectorMildPathTightness.path H hH0 (Z ω) (Y m ω)) :=
    Measure.map_congr (he m)
  simpa only [hm] using VectorMildPathTightness.tight_random_initial μ Z
    hZ Y hYm hYtight H hH0


include hH0 in
theorem tight (cap : ℝ) (hcap : 0 ≤ cap) (hCaps : ∀ m, NativeMatrixEquation.cap (G m) ≤ cap)
    (hEq : ∀ m, MatrixContinuousMild.Equation (G m) hH (N m) (U m) (hU m) u₀) :
    IsTightMeasureSet (Set.range (fun m => μ.map
      (NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hc m)))) := by
  exact tight_random F μ H hH hH0 G N U hU hc (fun _ => u₀) measurable_const cap hcap hCaps hEq

end SHEStochastic.MatrixSolutionPathTightness
