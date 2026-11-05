module

public import SHEStochastic.MatrixUnboundedGlobalEnergy
public import SHEStochastic.MatrixGlobalFourierWindow

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalFourierWindow
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

/-- Every unbounded block integral is the restriction of the ONE
coherent global Brownian integral on a larger physical horizon. -/
theorem integral (T : ℝ≥0) (k : ℕ) (hk : (k : ℝ≥0)*1+1≤T)
    (u : Process (E := Input (d := Fin n))
      (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration 1) ((k : ℝ≥0)*1))
      S.law.toMeasure 1) :
    (FiniteCylindricalIto.terminalIto (S.blocks k).toCoordinates
      MatrixPredictableHaarRotation.basis).integral u=
    (FiniteCylindricalIto.terminalIto (S.family T).toCoordinates
      MatrixPredictableHaarRotation.basis).integral
      (DeterministicItoShift.input (MatrixBlockNaturalFiltration.filtration 1)
        S.law.toMeasure T ((k : ℝ≥0)*1) 1 hk u) := by
  apply NativeDeterministicShift.integral hk
  intro i t ht
  funext p
  rw [← S.coherent (k+1) T]
  simpa only [mul_one] using S.driver k i t ht p

/-- The literal global state retains each local unbounded Fourier
equation after the block integral is moved to the global driver. -/
theorem equation (T : ℝ≥0) (k : ℕ) (hk : (k : ℝ≥0)*1+1≤T)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) (t : ℝ≥0) (ht : t≤1) :
    (fun p => Real.exp ((t : ℝ)*(m : ℝ)^2)*coordinate i a m
      (MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)*1+t) p)) =ᵐ[S.law.toMeasure]
      fun p => coordinate i a m (MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)*1) p)+
        (FiniteCylindricalIto.terminalIto (S.family T).toCoordinates
          MatrixPredictableHaarRotation.basis).integral
          (DeterministicItoShift.input (MatrixBlockNaturalFiltration.filtration 1)
            S.law.toMeasure T ((k : ℝ≥0)*1) 1 hk (StoppedItoInputs.stop
              (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration 1) ((k : ℝ≥0)*1))
              S.law.toMeasure 1 t (MatrixUnboundedFourierInput.input _ _ 1 G hG hβ hβ1.le
                (MatrixGlobalBlockFourier.state zero_lt_one k)
                (MatrixGlobalBlockFourier.predictable zero_lt_one k)
                (S.energy k) i a m))) p := by
  have he := S.equation k i a m t ht
  rw [integral S T k hk] at he
  filter_upwards [he] with p hp
  rw [MatrixGlobalBlockFourier.state_eq zero_lt_one k t ht] at hp
  have h0 := MatrixGlobalBlockFourier.state_eq zero_lt_one k 0 bot_le p
  simp only [add_zero] at h0
  exact hp.trans (congrArg (fun u => coordinate i a m u+_) h0)

end SHEStochastic.MatrixUnboundedGlobalFourierWindow
