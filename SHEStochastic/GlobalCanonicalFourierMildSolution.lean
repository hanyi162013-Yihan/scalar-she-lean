module

public import SHEStochastic.GlobalBoundedFourierRecognition
public import SHEStochastic.CanonicalNativeFourierRecognition
public import SHEStochastic.GlobalCompletedBoundedFourierSolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.GlobalCanonicalFourierMildSolution
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle CanonicalStateDriverFiltration
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {V ι : Type*} [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
  (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (filtration H) Q H
    (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

theorem fourier_equation
    (hH : 0<H)
    (hSolves : ∀ a n, CanonicalNativeFourierRecognition.Solves H Q hG hβ hβ1 B hb e hBrown a n) :
    GlobalBoundedFourierRecognition.FourierEquation (filtration H) Q H (state H) (state_predictable H)
      hG hβ hβ1 B hb (FiniteCylindricalIto.terminalIto
        (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e) (state H 0) := by
  intro T hTH a n
  have hh := hSolves a n T hTH
  convert hh using 1
  · funext x
    simp [CanonicalFourierFluctuation.value, state, clock, StoppedPathPasting.origin, min_eq_left hTH]
  · rfl

/-- The retained-driver Fourier equations yield a continuous native
mild solution on one closed-horizon event, with its actual initial state. -/
theorem exists_closed (hH : 0 < H)
    (hSolves : ∀ a n, CanonicalNativeFourierRecognition.Solves H Q hG hβ hβ1 B hb e hBrown a n) :
    GlobalBoundedFourierRecognition.HasClosedVersion (filtration H) Q H (state H) (state_predictable H)
      hG hβ hβ1 B hb hH (FiniteCylindricalIto.terminalIto
        (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e) (state H 0) :=
  GlobalBoundedFourierRecognition.exists_closed (filtration H) Q H (state H) (state_predictable H)
    hG hβ hβ1 B hb (CanonicalNativeFourierRecognition.family H Q hBrown) e (state H 0) hH
      (state_continuous H) (fourier_equation H Q hG hβ hβ1 B hb e hBrown hH hSolves)

/-- Only the countable real/imaginary Fourier basis is needed to build
the full conditional mild solution on one initial-state event. -/
theorem exists_closed_of_basis (hH : 0 < H)
    (hSolves : ∀ n : ℤ,
      CanonicalNativeFourierRecognition.Solves H Q hG hβ hβ1 B hb e hBrown Complex.reCLM n ∧
      CanonicalNativeFourierRecognition.Solves H Q hG hβ hβ1 B hb e hBrown Complex.imCLM n) :
    GlobalBoundedFourierRecognition.HasClosedVersion (filtration H) Q H (state H) (state_predictable H)
      hG hβ hβ1 B hb hH (FiniteCylindricalIto.terminalIto
        (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e) (state H 0) := by
  apply GlobalBoundedFourierRecognition.exists_closed_basis (filtration H) Q H (state H) (state_predictable H)
    hG hβ hβ1 B hb (CanonicalNativeFourierRecognition.family H Q hBrown) e (state H 0) hH (state_continuous H)
  intro T hTH a ha n
  have hh : CanonicalNativeFourierRecognition.Solves H Q hG hβ hβ1 B hb e hBrown a n := by
    rcases ha with rfl | rfl
    · exact (hSolves n).1
    · exact (hSolves n).2
  have ht := hh T hTH
  convert ht using 1
  · funext x
    simp [CanonicalFourierFluctuation.value, state, clock, StoppedPathPasting.origin, min_eq_left hTH]
  · rfl

set_option backward.isDefEq.respectTransparency true in
/-- The conditional native mild law has the exact joint cylinder
identity required by the continuation/pasting theorem. -/
theorem joint_problem (hH : 0 < H) 
    (hMild : GlobalBoundedFourierRecognition.HasClosedVersion (filtration H) Q H
      (state H) (state_predictable H) hG hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto
        (CanonicalNativeFourierRecognition.family H Q hBrown).toCoordinates e) (state H 0)) :
    JointFourierProblem.Holds hG hβ hβ1.le B B.property hb H e
      (Q.map (JointStateDriverPath.pack H)) := by
  intro s d a n driver f hf hSmooth hs
  let P := CanonicalNativeFourierRecognition.family H Q hBrown
  have hh : PastedCylinderMartingale.Identity (H)
      (JointFourierCylinderGenerator.test a n driver f hf hs)
      (JointFourierCylinderGenerator.generator hG hβ hβ1.le B B.property hb a n
        (fun j ↦ e (driver j)) driver f hf hs)
      (Q.map (UnboundedGlobalJointCanonicalPathMartingale.path (filtration H) Q H
        (state H) P (state_continuous H))) :=
    GlobalCompletedBoundedFourierSolution.joint_problem (filtration H) Q H (state H) (state_predictable H)
      hG hβ hβ1 B hb P e (state H 0) (state_adapted H 0).stronglyMeasurable
      Filter.EventuallyEq.rfl hH (state_continuous H) hMild a n driver f hf hSmooth hs
  simp only [UnboundedGlobalJointCanonicalPathMartingale.path] at hh
  have hc (t : StoppedPathPasting.Time H) : clock H t.val.toNNReal = t := by
    apply Subtype.ext
    change min ((t.val.toNNReal : ℝ≥0) : ℝ) (H : ℝ) = t.val
    rw [Real.coe_toNNReal _ t.property.1, min_eq_left t.property.2]
  have hpath : NativeContinuousPath.path H
      (UnboundedJointCylinderIdentification.joint (filtration H) Q H (state H) P)
      (UnboundedJointCylinderIdentification.continuous_joint (filtration H) Q H (state H) P
        (state_continuous H)) =ᵐ[Q] JointStateDriverPath.pack H := by
    filter_upwards [ae_all_iff.mpr fun i ↦ FiniteScalarIto.zero_ae P.toCoordinates i] with x hx
    apply ContinuousMap.ext
    intro t
    apply Prod.ext
    · change x.1 (clock H t.val.toNNReal) = x.1 t
      rw [hc]
    · funext i
      change coordinate H i t.val.toNNReal x-coordinate H i 0 x = x.2 i t
      have hz : coordinate H i 0 x = 0 := hx i
      rw [hz, sub_zero]
      change x.2 i (clock H t.val.toNNReal) = x.2 i t
      rw [hc]
  rw [Measure.map_congr hpath] at hh
  exact hh

end SHEStochastic.GlobalCanonicalFourierMildSolution
