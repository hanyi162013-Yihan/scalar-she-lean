module

public import SHEStochastic.MatrixRandomMildExistence
public import SHEStochastic.MatrixAnalyticObservation
public import SHEStochastic.MatrixStoppedNativeRows

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixMildObservations
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
    (G : MatrixNonlinearCoefficient.Coefficient d) (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (u₀ : Physical (d := d)) (hEq : MatrixContinuousMild.Equation G hH N U hU u₀)
local notation "Q" => NativeMatrixEquation.profile F G U hU
local notation "Qm" => NativeMatrixEquation.profile_measurable F G U hU
local notation "cap" => NativeMatrixEquation.cap G
local notation "cap0" => NativeMatrixEquation.cap_nonneg G
local notation "J" => FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis


/-- A genuine nonlinear L2 mild solution has the original-target
finite-Ito heat observations used in word iteration. Both the initial
mean and stochastic point input are identified, with no new equation. -/
theorem heat_observation_random
    (Z : Ω → Physical (d := d)) (hRandom : MatrixRandomMildExistence.Equation G hH N U hU Z) (s T : ℝ≥0) (hs : s ≤ H) (hT : T ≤ H) (hsT : s < T)
    (x : HeatCircle) (a : d) :
    (fun ω => VectorHeatObservation.observation ((T : ℝ)-(s : ℝ)) x (U (s,ω)) a) =ᵐ[μ]
      fun ω => VectorHeatObservation.observation (T : ℝ) x (Z ω) a+
        (J).integral (StoppedItoInputs.stop F μ H (s : ℝ)
          (MatrixPointHeatInput.input F μ H hH cap cap0 Q (fun _ => le_rfl) Qm T hT x a)) ω := by
  have h := MatrixAnalyticObservation.observation_ae F μ H hH cap cap0 Q (fun _ => le_rfl) Qm
    s T hs hT hsT x a N
  have hm (z : Physical (d := d)) : VectorHeatObservation.observation ((T : ℝ)-(s : ℝ)) x (VectorAnalyticHeat.heat (s : ℝ) z)=
      VectorHeatObservation.observation (T : ℝ) x z := by
    calc
      _ = VectorHeatObservation.observation ((T : ℝ)-(s : ℝ)+(s : ℝ)) x z :=
        VectorAnalyticHeat.observation (ε := (T : ℝ)-(s : ℝ)) (t := (s : ℝ))
          (sub_pos.mpr hsT) s.2 x z
      _ = _ := congrArg (fun r : ℝ => VectorHeatObservation.observation r x z) (by ring)
  filter_upwards [hRandom s hs,h] with ω hω hη
  rw [hω,map_add,PiLp.add_apply,hm (Z ω)]
  exact congrArg (fun r : ℝ => VectorHeatObservation.observation (T : ℝ) x (Z ω) a+r) hη


include hEq in
theorem heat_observation (s T : ℝ≥0) (hs : s ≤ H) (hT : T ≤ H) (hsT : s < T)
    (x : HeatCircle) (a : d) :
    (fun ω => VectorHeatObservation.observation ((T : ℝ)-(s : ℝ)) x (U (s,ω)) a) =ᵐ[μ]
      fun ω => VectorHeatObservation.observation (T : ℝ) x u₀ a+
        (J).integral (StoppedItoInputs.stop F μ H (s : ℝ)
          (MatrixPointHeatInput.input F μ H hH cap cap0 Q (fun _ => le_rfl) Qm T hT x a)) ω := by
  exact heat_observation_random G hH N U hU (fun _ => u₀) hEq s T hs hT hsT x a

include hEq in
/-- Every finite original stopped heat history of the actual nonlinear
solution is represented by its actual native rows on the same space.
Targets, centers, colors and repeated observations remain unchanged. -/
theorem finite_history {k : ℕ} (σ T : Fin k → ℝ≥0) (hT : ∀ i, T i ≤ H)
    (hgap : ∀ i, σ i < T i) (x : Fin k → HeatCircle) (color : Fin k → d) :
    (fun ω => (WithLp.toLp 2 (fun i => VectorHeatObservation.observation ((T i : ℝ)-(σ i : ℝ))
      (x i) (U (σ i,ω)) (color i)) : WordRecursion.State k)) =ᵐ[μ]
      fun ω => WithLp.toLp 2 (fun i => VectorHeatObservation.observation (T i : ℝ) (x i) u₀ (color i)+
        (J).integral (MatrixStoppedNativeRows.input F μ H hH cap cap0 (fun _ => Q) (fun _ _ => le_rfl)
          (fun _ => Qm) σ T hT x color i) ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => heat_observation G hH N U hU u₀ hEq
    (σ i) (T i) ((hgap i).le.trans (hT i)) (hT i) (hgap i) (x i) (color i))] with ω hω
  ext i
  exact hω i

end SHEStochastic.MatrixMildObservations
