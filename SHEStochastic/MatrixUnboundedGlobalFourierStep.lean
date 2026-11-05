module

public import SHEStochastic.MatrixUnboundedGlobalFourierWindow
public import SHEStochastic.MatrixUnboundedFourierShiftInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalFourierStep
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

def state : ℝ≥0×MatrixGlobalBlockPath.Space (n := n) 1 → Physical (d := Fin n) :=
  fun p => MatrixGlobalBlockPath.state 1 p.1 p.2

theorem predictable :
    StronglyMeasurable[(MatrixBlockNaturalFiltration.filtration (n := n) 1).predictable]
      (state (n := n)) := MatrixBlockProcessAdapted.state_predictable 1 zero_lt_one

def input (T : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    Process (E := Input (d := Fin n)) (MatrixBlockNaturalFiltration.filtration 1)
      S.law.toMeasure T :=
  MatrixUnboundedFourierInput.input _ _ T G hG hβ hβ1.le state predictable
    (MatrixUnboundedGlobalEnergy.finite_energy S T) i a m

def integral (T : ℝ≥0) := FiniteCylindricalIto.terminalIto
  (S.family T).toCoordinates MatrixPredictableHaarRotation.basis

def value (T t : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    MatrixGlobalBlockPath.Space (n := n) 1 → ℝ :=
  (integral S T).integral
    (StoppedItoInputs.stop (MatrixBlockNaturalFiltration.filtration 1)
      S.law.toMeasure T t (input S T i a m))

/-- One unbounded vector Fourier equation pastes across the next
physical block as a difference of the SAME global Itô integral. -/
theorem step (T : ℝ≥0) (k : ℕ) (hk : (k : ℝ≥0)*1+1≤T)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) (t : ℝ≥0) (ht : t≤1) :
    (fun p => Real.exp ((((k : ℝ≥0)*1+t : ℝ≥0) : ℝ)*(m : ℝ)^2)*coordinate i a m
      (MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)*1+t) p)) =ᵐ[S.law.toMeasure]
      fun p => Real.exp ((((k : ℝ≥0)*1 : ℝ≥0) : ℝ)*(m : ℝ)^2)*coordinate i a m
        (MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)*1) p)+
        value S T ((k : ℝ≥0)*1+t) i a m p-value S T ((k : ℝ≥0)*1) i a m p := by
  let F := MatrixBlockNaturalFiltration.filtration (n := n) 1
  let μ := S.law.toMeasure
  let v : ℝ≥0 := (k : ℝ≥0)*1
  let c := Real.exp ((v : ℝ)*(m : ℝ)^2)
  let localInput := MatrixUnboundedFourierInput.input (DeterministicItoShift.filtration F v) μ 1
    G hG hβ hβ1.le (MatrixGlobalBlockFourier.state zero_lt_one k)
    (MatrixGlobalBlockFourier.predictable zero_lt_one k) (S.energy k) i a m
  let localStop := StoppedItoInputs.stop (DeterministicItoShift.filtration F v) μ 1 t localInput
  let extended := DeterministicItoShift.input F μ T v 1 hk localStop
  let J := integral S T
  let globalInput := input S T i a m
  let endStop := StoppedItoInputs.stop F μ T (v+t) globalInput
  let startStop := StoppedItoInputs.stop F μ T v globalInput
  have hi : c • extended=endStop-startStop := by
    exact MatrixUnboundedFourierShiftInput.stopped F μ T v 1 hk
      G hG hβ hβ1.le state (MatrixGlobalBlockFourier.state zero_lt_one k)
      predictable (MatrixGlobalBlockFourier.predictable zero_lt_one k)
      (MatrixUnboundedGlobalEnergy.finite_energy S T) (S.energy k)
      (fun s hs p => MatrixGlobalBlockFourier.state_eq zero_lt_one k s hs p)
      i a m t ht
  have hJ : c • J.integral extended=J.integral endStop-J.integral startStop := by
    rw [←map_smul,hi,map_sub]
  have hs := Lp.coeFn_smul c (J.integral extended)
  have hd := Lp.coeFn_sub (J.integral endStop) (J.integral startStop)
  rw [←hJ] at hd
  have he := MatrixUnboundedGlobalFourierWindow.equation S T k hk i a m t ht
  filter_upwards [he,hs,hd] with p hp hs hd
  change Real.exp ((t : ℝ)*(m : ℝ)^2)*coordinate i a m
    (MatrixGlobalBlockPath.state 1 (v+t) p)=
      coordinate i a m (MatrixGlobalBlockPath.state 1 v p)+J.integral extended p at hp
  have hnoise : c*J.integral extended p=J.integral endStop p-J.integral startStop p := by
    exact hs.symm.trans hd
  have hc : Real.exp ((((k : ℝ≥0)*1+t : ℝ≥0) : ℝ)*(m : ℝ)^2)=
      c*Real.exp ((t : ℝ)*(m : ℝ)^2) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [c,v]
    push_cast
    ring
  change Real.exp ((((k : ℝ≥0)*1+t : ℝ≥0) : ℝ)*(m : ℝ)^2)*_=
    c*_+J.integral endStop p-J.integral startStop p
  rw [hc,mul_assoc,hp,mul_add,hnoise]
  ring

end SHEStochastic.MatrixUnboundedGlobalFourierStep
