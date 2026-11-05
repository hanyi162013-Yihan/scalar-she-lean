module

public import SHEStochastic.MatrixGlobalFourierWindow
public import SHEStochastic.MatrixFourierShiftInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixGlobalFourierStep
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

def state : ℝ≥0×MatrixGlobalBlockPath.Space (n := n) H → Physical (d := Fin n) :=
  fun p => MatrixGlobalBlockPath.state H p.1 p.2

include hH0 in
theorem predictable : StronglyMeasurable[(MatrixBlockNaturalFiltration.filtration (n := n) H).predictable]
    (state (n := n) (H := H)) := MatrixBlockProcessAdapted.state_predictable H hH0

def input (T : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    Process (E := Input (d := Fin n)) (MatrixBlockNaturalFiltration.filtration H) (D.base.law ρ₀) T :=
  MatrixFourierInput.input _ _ T (MatrixSmoothCoefficient.coefficient G 0)
    (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1 state (predictable hH0) i a m

def integral (T : ℝ≥0) := FiniteCylindricalIto.terminalIto
  (MatrixGlobalBrownianPast.family D.base ρ₀ hH0 T).toCoordinates MatrixPredictableHaarRotation.basis

def value (T t : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    MatrixGlobalBlockPath.Space (n := n) H → ℝ :=
  (integral D ρ₀ hH0 T).integral
    (StoppedItoInputs.stop (MatrixBlockNaturalFiltration.filtration H) (D.base.law ρ₀) T t (input D ρ₀ hH0 T i a m))

/-- The physical integrating-factor equation pastes across one whole
block by the difference of two stopped values of the SAME global
native Itô integral. -/
theorem step (T : ℝ≥0) (k : ℕ) (hk : (k : ℝ≥0)*H+H≤T)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) (t : ℝ≥0) (ht : t≤H) :
    (fun p => Real.exp ((((k : ℝ≥0)*H+t : ℝ≥0) : ℝ)*(m : ℝ)^2)*coordinate i a m
      (MatrixGlobalBlockPath.state H ((k : ℝ≥0)*H+t) p)) =ᵐ[D.base.law ρ₀]
      fun p => Real.exp ((((k : ℝ≥0)*H : ℝ≥0) : ℝ)*(m : ℝ)^2)*coordinate i a m
        (MatrixGlobalBlockPath.state H ((k : ℝ≥0)*H) p)+
        value D ρ₀ hH0 T ((k : ℝ≥0)*H+t) i a m p-value D ρ₀ hH0 T ((k : ℝ≥0)*H) i a m p := by
  let F := MatrixBlockNaturalFiltration.filtration (n := n) H
  let μ := D.base.law ρ₀
  let v : ℝ≥0 := (k : ℝ≥0)*H
  let c := Real.exp ((v : ℝ)*(m : ℝ)^2)
  let localInput := MatrixFourierInput.input (DeterministicItoShift.filtration F v) μ H
    (MatrixSmoothCoefficient.coefficient G 0) (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
    (MatrixGlobalBlockFourier.state hH0 k) (MatrixGlobalBlockFourier.predictable hH0 k) i a m
  let localStop := StoppedItoInputs.stop (DeterministicItoShift.filtration F v) μ H t localInput
  let extended := DeterministicItoShift.input F μ T v H hk localStop
  let J := integral D ρ₀ hH0 T
  let globalInput := input D ρ₀ hH0 T i a m
  let endStop := StoppedItoInputs.stop F μ T (v+t) globalInput
  let startStop := StoppedItoInputs.stop F μ T v globalInput
  have hi : c • extended=endStop-startStop := by
    exact MatrixFourierShiftInput.stopped F μ T v H hk (MatrixSmoothCoefficient.coefficient G 0)
      (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1 state (MatrixGlobalBlockFourier.state hH0 k)
      (predictable hH0) (MatrixGlobalBlockFourier.predictable hH0 k)
      (fun s hs p => MatrixGlobalBlockFourier.state_eq hH0 k s hs p) i a m t ht
  have hJ : c • J.integral extended=J.integral endStop-J.integral startStop := by
    rw [←map_smul,hi,map_sub]
  have hs := Lp.coeFn_smul c (J.integral extended)
  have hd := Lp.coeFn_sub (J.integral endStop) (J.integral startStop)
  rw [←hJ] at hd
  have he := MatrixGlobalFourierWindow.equation D ρ₀ hH0 T k hk i a m t ht
  filter_upwards [he,hs,hd] with p hp hs hd
  change Real.exp ((t : ℝ)*(m : ℝ)^2)*coordinate i a m
    (MatrixGlobalBlockPath.state H (v+t) p)=
      coordinate i a m (MatrixGlobalBlockPath.state H v p)+J.integral extended p at hp
  have hnoise : c*J.integral extended p=J.integral endStop p-J.integral startStop p := by
    exact hs.symm.trans hd
  have hc : Real.exp ((((k : ℝ≥0)*H+t : ℝ≥0) : ℝ)*(m : ℝ)^2)=c*Real.exp ((t : ℝ)*(m : ℝ)^2) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [c,v]
    push_cast
    ring
  change Real.exp ((((k : ℝ≥0)*H+t : ℝ≥0) : ℝ)*(m : ℝ)^2)*_=c*_+J.integral endStop p-J.integral startStop p
  rw [hc,mul_assoc,hp,mul_add,hnoise]
  ring

end SHEStochastic.MatrixGlobalFourierStep
