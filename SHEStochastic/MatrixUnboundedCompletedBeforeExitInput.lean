module

public import SHEStochastic.MatrixUnboundedLocalizedInputTransport
public import SHEStochastic.MatrixUnboundedFourierInputLocality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCompletedBeforeExitInput
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := borel _
local instance : BorelSpace
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi))) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ S.law.toMeasure
    (MatrixBlockNaturalFiltration.filtration 1)
local notation "μc" => IndependentNoiseCompletion.measure ρ S.law.toMeasure
local instance (priority := 2000) completedSigma :
    MeasurableSpace (RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :=
  MatrixUnboundedCompletedGlobal.completedSigma S

/-- Finite square energy of the completed global state. -/
theorem global_energy (H : ℝ≥0) :
    Integrable (fun p => ‖MatrixUnboundedCompletedGlobal.state S p‖^2)
      (energyMeasure μc H) :=
  MatrixUnboundedFourierPullback.energy
    (Ξ := RandomInitialBrownianFamily.Space ρ S.law.toMeasure)
    (mΞ := completedSigma S) Prod.snd
    (IndependentNoiseCompletion.snd_preserving ρ S.law.toMeasure)
    MatrixUnboundedGlobalFourierStep.state (MatrixUnboundedGlobalEnergy.finite_energy S H)

/-- The pulled-back localized vector path is the actual unbounded
global vector path strictly before its L2 exit. -/
theorem state_before_exit (N : ℕ)
    (p : ℝ≥0 × RandomInitialBrownianFamily.Space ρ S.law.toMeasure)
    (hp : (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit
      (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N p.2) :
    MatrixUnboundedLocalizedInputTransport.unitState S N p =
      MatrixUnboundedCompletedGlobal.state S p := by
  change (VectorNativeHaarBasis.equivalence (n := n)).symm
      (UnboundedL2Localization.state
        (MatrixUnboundedCompletedLocalField.nativeState S) N p) = _
  rw [UnboundedL2Localization.agrees_before_exit
    (MatrixUnboundedCompletedLocalField.nativeState S)
    (MatrixUnboundedCompletedLocalField.native_continuous S) N p hp]
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- The original unbounded matrix noise rows agree before each L2 exit
after transporting the local heat field back to the unit circle. -/
theorem input (H : ℝ≥0) (N : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    ∀ᵐ p ∂energyMeasure μc H,
      (p.1 : WithTop ℝ≥0) < ContinuousNormExit.exit
        (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N p.2 →
      MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
        (MatrixUnboundedLocalizedInputTransport.unitState S N)
        (MatrixUnboundedLocalizedInputTransport.predictable S N)
        (MatrixUnboundedLocalizedInputTransport.energy S H N) i a m p =
      MatrixUnboundedFourierInput.input (Fc) μc H G hG hβ hβ1.le
        (MatrixUnboundedCompletedGlobal.state S)
        (MatrixUnboundedCompletedGlobal.predictable S)
        (global_energy S H) i a m p := by
  exact MatrixUnboundedFourierInputLocality.input (Fc) μc H G hG hβ hβ1.le
    (MatrixUnboundedLocalizedInputTransport.unitState S N)
    (MatrixUnboundedCompletedGlobal.state S)
    (MatrixUnboundedLocalizedInputTransport.predictable S N)
    (MatrixUnboundedCompletedGlobal.predictable S)
    (MatrixUnboundedLocalizedInputTransport.energy S H N) (global_energy S H)
    (ContinuousNormExit.exit
      (fun t ω => MatrixUnboundedCompletedLocalField.nativeState S (t,ω)) N)
    (Filter.Eventually.of_forall fun p hp => state_before_exit S N p hp) i a m

end SHEStochastic.MatrixUnboundedCompletedBeforeExitInput
