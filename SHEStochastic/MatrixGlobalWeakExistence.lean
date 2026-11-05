module

public import SHEStochastic.MatrixGlobalFourierEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixGlobalWeakExistence
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

theorem initial_law {H : ℝ≥0}
    {Supports : ProbabilityMeasure (MatrixLocalBlockChain.Space (n := n) H) → Prop}
    (D : MatrixCanonicalBlockChain.Data H Supports)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (hH0 : 0<H) :
    (D.law ρ₀).map (MatrixGlobalBlockPath.state H 0)=ρ₀.val.toMeasure := by
  have hp := MatrixGlobalBlockBundle.preserving D ρ₀ (hH0 := hH0) 0
  have hm := MatrixLocalBlockChain.state_measurable (n := n) H 0
  have he : (MatrixLocalBlockChain.state H 0 ∘ MatrixGlobalBlockBundle.bundle H hH0 0)=
      MatrixGlobalBlockPath.state (n := n) H 0 := by
    funext p
    change MatrixGlobalBlockFourier.state hH0 0 (0,p)=MatrixGlobalBlockPath.state H 0 p
    have hh := MatrixGlobalBlockFourier.state_eq (n := n) hH0 0 0 bot_le p
    simpa only [Nat.cast_zero,zero_mul,add_zero] using hh
  rw [←he,←Measure.map_map hm hp.measurable,hp.map_eq]
  exact D.initial_law ρ₀ 0

/-- A single global continuous predictable state with the prescribed
L2 initial law, all finite-time L2 moments, a Brownian driver in the
full physical filtration, and its native Fourier equation on every
finite union of blocks. The coefficient is the canonical positive
square diffusion with the original covariance. -/
structure Solution (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1) (hH0 : 0<H)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) where
  law : ProbabilityMeasure (MatrixGlobalBlockPath.Space (n := n) H)
  initial : law.toMeasure.map (MatrixGlobalBlockPath.state H 0)=ρ₀.val.toMeasure
  moments : ∀ t,MemLp (MatrixGlobalBlockPath.state H t) 2 law.toMeasure
  family : ∀ T : ℝ≥0,FiniteScalarIto.Family (MatrixBlockNaturalFiltration.filtration H) law.toMeasure T (Fin n×HaarNode)
  equation : ∀ M : ℕ,MatrixFourierMildRealization.RandomEquation (MatrixBlockNaturalFiltration.filtration H) law.toMeasure
    ((M : ℝ≥0)*H) (MatrixSmoothCoefficient.coefficient G 0)
    (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    MatrixGlobalFourierStep.state (MatrixGlobalFourierStep.predictable hH0) (family ((M : ℝ≥0)*H))
    (MatrixGlobalBlockPath.state H 0)

theorem exists_solution {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1) (hH : (H : ℝ)≤1) (hH0 : 0<H)
    (N : FiniteScalarIto.Family F μ H (Fin n×HaarNode)) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) :
    Nonempty (Solution H G hG hβ hβ1 hH0 ρ₀) := by
  obtain ⟨D⟩ := MatrixFourierBlockChain.exists_data F μ H G hG hβ hβ1 hH hH0 N
  exact ⟨⟨⟨D.base.law ρ₀,inferInstance⟩,initial_law D.base ρ₀ hH0,
    MatrixGlobalBlockPath.memLp D.base ρ₀ hH0,MatrixGlobalBrownianPast.family D.base ρ₀ hH0,
    MatrixGlobalFourierEquation.equation D ρ₀ hH0⟩⟩

/-- The construction actually uses one global canonical driver. Its
finite-horizon families have identical coordinate paths, rather than
merely the same coordinate laws. -/
theorem exists_coherent_solution {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1) (hH : (H : ℝ)≤1) (hH0 : 0<H)
    (N : FiniteScalarIto.Family F μ H (Fin n×HaarNode)) (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) :
    ∃ S : Solution H G hG hβ hβ1 hH0 ρ₀,∀ T K,(S.family T).W=(S.family K).W := by
  obtain ⟨D⟩ := MatrixFourierBlockChain.exists_data F μ H G hG hβ hβ1 hH hH0 N
  let S : Solution H G hG hβ hβ1 hH0 ρ₀ :=
    ⟨⟨D.base.law ρ₀,inferInstance⟩,initial_law D.base ρ₀ hH0,
      MatrixGlobalBlockPath.memLp D.base ρ₀ hH0,MatrixGlobalBrownianPast.family D.base ρ₀ hH0,
      MatrixGlobalFourierEquation.equation D ρ₀ hH0⟩
  exact ⟨S,fun _ _ => rfl⟩

variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β≤1} {hH0 : 0<H}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)} (S : Solution H G hG hβ hβ1 hH0 ρ₀)

include hH0 in
theorem continuous (p : MatrixGlobalBlockPath.Space (n := n) H) :
    Continuous (fun t => MatrixGlobalBlockPath.state H t p) := MatrixGlobalBlockPath.continuous H hH0 p

/-- On the original analytic horizon the global Fourier solution is
the actual Hilbert-valued mild solution, by the existing reconstruction. -/
theorem mild (M : ℕ) (hMH : (((M : ℝ≥0)*H : ℝ≥0) : ℝ)≤1) :
    MatrixFourierMildRecognition.Equation (MatrixBlockNaturalFiltration.filtration H) S.law.toMeasure
      ((M : ℝ≥0)*H) (MatrixSmoothCoefficient.coefficient G 0) MatrixGlobalFourierStep.state
      (MatrixGlobalFourierStep.predictable hH0) hMH (S.family ((M : ℝ≥0)*H)) (MatrixGlobalBlockPath.state H 0) :=
  MatrixFourierMildRecognition.equation _ _ _ _ (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    _ _ hMH _ _ (S.equation M)

end SHEStochastic.MatrixGlobalWeakExistence
