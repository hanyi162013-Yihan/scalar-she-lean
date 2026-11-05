module

public import SHEStochastic.MatrixGlobalBlockFourier
public import SHEStochastic.NativeDeterministicShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixGlobalFourierWindow
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
variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β≤1} {hH : (H : ℝ)≤1}
    (D : MatrixFourierBlockChain.Data H G hG hβ hβ1 hH)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (hH0 : 0<H)

/-- Every native local integral is literally the global native integral
on its deterministic physical block; the two integrals share all
state-dependent predictable integrands. -/
theorem integral (T : ℝ≥0) (k : ℕ) (hk : (k : ℝ≥0)*H+H≤T)
    (u : Process (E := Input (d := Fin n))
      (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H)) (D.base.law ρ₀) H) :
    (FiniteCylindricalIto.terminalIto (MatrixGlobalBlockFamily.family D.base ρ₀ hH0 k).toCoordinates
      MatrixPredictableHaarRotation.basis).integral u=
    (FiniteCylindricalIto.terminalIto (MatrixGlobalBrownianPast.family D.base ρ₀ hH0 T).toCoordinates
      MatrixPredictableHaarRotation.basis).integral
      (DeterministicItoShift.input (MatrixBlockNaturalFiltration.filtration H) (D.base.law ρ₀) T
        ((k : ℝ≥0)*H) H hk u) := by
  apply NativeDeterministicShift.integral hk
  intro i t ht
  funext p
  exact CanonicalStateDriverFiltration.coordinate_bundle H (MatrixGlobalBlockPath.state H)
    (MatrixGlobalBlockPath.continuous H hH0) (MatrixGlobalBlockPath.driver H)
    (MatrixGlobalBlockPath.driver_continuous H hH0) ((k : ℝ≥0)*H) t ht i p

/-- The literal global state solves its local Fourier equation with
the global integral, not merely with a separately chosen restart noise. -/
theorem equation (T : ℝ≥0) (k : ℕ) (hk : (k : ℝ≥0)*H+H≤T)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) (t : ℝ≥0) (ht : t≤H) :
    (fun p => Real.exp ((t : ℝ)*(m : ℝ)^2)*coordinate i a m
      (MatrixGlobalBlockPath.state H ((k : ℝ≥0)*H+t) p)) =ᵐ[D.base.law ρ₀]
      fun p => coordinate i a m (MatrixGlobalBlockPath.state H ((k : ℝ≥0)*H) p)+
        (FiniteCylindricalIto.terminalIto (MatrixGlobalBrownianPast.family D.base ρ₀ hH0 T).toCoordinates
          MatrixPredictableHaarRotation.basis).integral
          (DeterministicItoShift.input (MatrixBlockNaturalFiltration.filtration H) (D.base.law ρ₀) T
            ((k : ℝ≥0)*H) H hk (StoppedItoInputs.stop
              (DeterministicItoShift.filtration (MatrixBlockNaturalFiltration.filtration H) ((k : ℝ≥0)*H))
              (D.base.law ρ₀) H t (MatrixFourierInput.input _ _ H (MatrixSmoothCoefficient.coefficient G 0)
                (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
                (MatrixGlobalBlockFourier.state hH0 k) (MatrixGlobalBlockFourier.predictable hH0 k) i a m))) p := by
  have he := MatrixGlobalBlockFourier.equation D ρ₀ hH0 k i a m t ht
  rw [integral D ρ₀ hH0 T k hk] at he
  filter_upwards [he] with p hp
  rw [MatrixGlobalBlockFourier.state_eq hH0 k t ht] at hp
  have h0 := MatrixGlobalBlockFourier.state_eq hH0 k 0 bot_le p
  simp only [add_zero] at h0
  exact hp.trans (congrArg (fun u => coordinate i a m u+_) h0)

end SHEStochastic.MatrixGlobalFourierWindow
