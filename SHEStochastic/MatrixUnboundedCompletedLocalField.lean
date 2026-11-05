module

public import SHEStochastic.MatrixUnboundedCompletedGlobal
public import SHEStochastic.UnboundedGlobalLocalVersion
public import SHEStochastic.VectorNativeHaarBasis
public import SHEStochastic.MatrixDiffusionRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCompletedLocalField
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar HeatParameterCover HeatParameterCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
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

/-- The original global vector path, written on the native 2π circle. -/
def nativeState (z : ℝ≥0 × RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (AddCircle.haarAddCircle (T := 2*Real.pi)) :=
  VectorNativeHaarBasis.equivalence (MatrixUnboundedCompletedGlobal.state S z)

theorem native_predictable : StronglyMeasurable[(Fc).predictable] (nativeState S) :=
  (VectorNativeHaarBasis.equivalence (n := n)).continuous.comp_stronglyMeasurable
    (MatrixUnboundedCompletedGlobal.predictable S)

theorem native_continuous (ω : RandomInitialBrownianFamily.Space ρ S.law.toMeasure) :
    Continuous (fun t => nativeState S (t,ω)) :=
  (VectorNativeHaarBasis.equivalence (n := n)).continuous.comp
    (MatrixGlobalBlockPath.continuous 1 zero_lt_one ω.2)

/-- Each original unbounded matrix row has a continuous, adapted local
stochastic heat field on every finite horizon, using the SAME coherent
Brownian family as the completed global Fourier equation. -/
theorem exists_row_field (H : ℝ≥0) (i : Fin n) :
    ∃ Y : Parameter → RandomInitialBrownianFamily.Space ρ S.law.toMeasure → ℝ,
      (∀ p, Measurable (Y p)) ∧
      (∀ p, StronglyMeasurable[(Fc) (GlobalHeatParameter.time H p)] (Y p)) ∧
      (∀ ω, Continuous (fun p => Y p ω)) ∧
      (∀ N p, ∀ᵐ ω ∂μc,
        (GlobalHeatParameter.time H p : WithTop ℝ≥0) <
          ContinuousNormExit.exit (fun t ω => nativeState S (t,ω)) N ω →
        Y p ω = UnboundedGlobalLocalVersion.observation (Fc) (nativeState S)
          (native_predictable S) (MatrixDiffusionRows.holder hG i) hβ hβ1 (μc) H
          (MatrixUnboundedCompletedGlobal.family S H) (VectorNativeHaarBasis.basis (n := n)) N p ω) ∧
      ∀ᵐ ω ∂μc, (∀ p, Y (zeroTime p) ω=0) ∧
        (∃ M : ℝ, 0≤M ∧ ∀ p, |Y p ω|≤M) ∧
        ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ p : Parameter, |p.val 0|<δ → |Y p ω|<ε := by
  exact UnboundedGlobalLocalVersion.exists_version (Fc) (nativeState S)
    (native_predictable S) (MatrixDiffusionRows.holder hG i) hβ hβ1 (μc) H
    (MatrixUnboundedCompletedGlobal.family S H) (VectorNativeHaarBasis.basis (n := n))
    (native_continuous S) (MatrixUnboundedCompletedGlobal.contains_null S)

end SHEStochastic.MatrixUnboundedCompletedLocalField
