module

public import SHEStochastic.MatrixUnboundedGlobalFourierAll
public import SHEStochastic.RandomVectorHeatInitialProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalRemainder
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

/-- The candidate Hilbert stochastic convolution is already a concrete
random Hilbert vector: state minus the deterministic heat orbit. -/
def value (T : ℝ≥0) (p : MatrixGlobalBlockPath.Space (n := n) 1) : Physical (d := Fin n) :=
  MatrixGlobalBlockPath.state 1 T p-
    VectorAnalyticHeat.heat (T : ℝ) (MatrixGlobalBlockPath.state 1 0 p)

/-- The candidate convolution is predictable in the original global
filtration, including at time zero. -/
theorem predictable :
    StronglyMeasurable[(MatrixBlockNaturalFiltration.filtration (n := n) 1).predictable]
      (fun z : ℝ≥0 × MatrixGlobalBlockPath.Space (n := n) 1 => value (n := n) z.1 z.2) := by
  have hinitial : StronglyMeasurable[(MatrixBlockNaturalFiltration.filtration (n := n) 1) 0]
      (MatrixGlobalBlockPath.state 1 0) :=
    MatrixBlockProcessAdapted.state_adapted 1 zero_lt_one 0
  exact (MatrixBlockProcessAdapted.state_predictable 1 zero_lt_one).sub
    (RandomVectorHeatInitialProcess.predictable
      (MatrixBlockNaturalFiltration.filtration (n := n) 1)
      (MatrixGlobalBlockPath.state 1 0) hinitial)

/-- Its trajectories are continuous, as the difference of the global
state and its initial heat orbit. -/
theorem continuous_paths (p : MatrixGlobalBlockPath.Space (n := n) 1) :
    Continuous (fun T : ℝ≥0 => value (n := n) T p) :=
  (MatrixGlobalBlockPath.continuous 1 zero_lt_one p).sub
    (RandomVectorHeatInitialProcess.continuous_paths
      (MatrixGlobalBlockPath.state 1 0) p)

theorem mild_decomposition (T : ℝ≥0) (p : MatrixGlobalBlockPath.Space (n := n) 1) :
    MatrixGlobalBlockPath.state 1 T p =
      VectorAnalyticHeat.heat (T : ℝ) (MatrixGlobalBlockPath.state 1 0 p)+value (n := n) T p := by
  simp only [value]
  abel

theorem memLp (T : ℝ≥0) : MemLp (value (n := n) T) 2 S.law.toMeasure :=
  (S.moments T).sub ((VectorAnalyticHeat.heat (T : ℝ)).comp_memLp' (S.moments 0))

/-- Every literal Fourier coordinate of the Hilbert remainder equals
the actual unbounded scalar Ito integral, with the heat damping exposed. -/
theorem fourier_coordinate (T : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (fun p => MatrixFourierCoordinates.coordinate i a m (value (n := n) T p)) =ᵐ[S.law.toMeasure]
      fun p => Real.exp (-(T : ℝ)*(m : ℝ)^2)*
        MatrixUnboundedGlobalFourierStep.value S T T i a m p := by
  let c := Real.exp (-(T : ℝ)*(m : ℝ)^2)
  have hc : c*Real.exp ((T : ℝ)*(m : ℝ)^2)=1 := by
    unfold c
    rw [←Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  filter_upwards [MatrixUnboundedGlobalFourierAll.equation S T i a m T le_rfl] with p hp
  change Real.exp ((T : ℝ)*(m : ℝ)^2)*coordinate i a m
    (MatrixGlobalBlockPath.state 1 T p)=coordinate i a m
      (MatrixGlobalBlockPath.state 1 0 p)+MatrixUnboundedGlobalFourierStep.value S T T i a m p at hp
  change coordinate i a m
    (MatrixGlobalBlockPath.state 1 T p-
      VectorAnalyticHeat.heat (T : ℝ) (MatrixGlobalBlockPath.state 1 0 p)) = _
  rw [map_sub]
  have hheat := MatrixFourierCoordinates.coordinate_heat i a m T.property
    (MatrixGlobalBlockPath.state 1 0 p)
  calc
    _ = coordinate i a m (MatrixGlobalBlockPath.state 1 T p)-
          c*coordinate i a m (MatrixGlobalBlockPath.state 1 0 p) := by
      exact congrArg (fun y : ℝ => coordinate i a m (MatrixGlobalBlockPath.state 1 T p)-y) hheat
    _ = c*(Real.exp ((T : ℝ)*(m : ℝ)^2)*coordinate i a m (MatrixGlobalBlockPath.state 1 T p)-
          coordinate i a m (MatrixGlobalBlockPath.state 1 0 p)) := by
      rw [mul_sub,←mul_assoc,hc,one_mul]
    _ = _ := by rw [hp]; ring

/-- At a fixed time the Fourier stochastic integrals determine the
Hilbert remainder uniquely; only the countable real/imaginary Fourier
tests are needed. -/
theorem unique (T : ℝ≥0)
    (V : MatrixGlobalBlockPath.Space (n := n) 1 → Physical (d := Fin n))
    (hRe : ∀ i m,
      (fun p => coordinate i Complex.reCLM m (V p)) =ᵐ[S.law.toMeasure]
        fun p => Real.exp (-(T : ℝ)*(m : ℝ)^2)*
          MatrixUnboundedGlobalFourierStep.value S T T i Complex.reCLM m p)
    (hIm : ∀ i m,
      (fun p => coordinate i Complex.imCLM m (V p)) =ᵐ[S.law.toMeasure]
        fun p => Real.exp (-(T : ℝ)*(m : ℝ)^2)*
          MatrixUnboundedGlobalFourierStep.value S T T i Complex.imCLM m p) :
    V =ᵐ[S.law.toMeasure] value (n := n) T := by
  apply MatrixFourierCoordinates.ae_eq S.law.toMeasure V (value (n := n) T)
  · intro i m
    exact (hRe i m).trans (fourier_coordinate S T i Complex.reCLM m).symm
  · intro i m
    exact (hIm i m).trans (fourier_coordinate S T i Complex.imCLM m).symm

end SHEStochastic.MatrixUnboundedGlobalRemainder
