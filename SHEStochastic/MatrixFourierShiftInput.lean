module

public import SHEStochastic.DeterministicWindowInput
public import SHEStochastic.MatrixFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFourierShiftInput
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T v h : ℝ≥0) (hvh : v+h≤T)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1)
    (U V : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (hV : StronglyMeasurable[(DeterministicItoShift.filtration F v).predictable] V)
    (hState : ∀ t,t≤h → ∀ ω,V (t,ω)=U (v+t,ω))

include hState in
/-- The local Fourier integrating factor differs from the global one
by exp(v*m^2). The literal stopped state-dependent inputs therefore
paste by subtracting the two original global stopped inputs. -/
theorem stopped (i : d) (a : ℂ →L[ℝ] ℝ) (m : ℤ) (t : ℝ≥0) (ht : t≤h) :
    Real.exp ((v : ℝ)*(m : ℝ)^2) • DeterministicItoShift.input F μ T v h hvh
      (StoppedItoInputs.stop (DeterministicItoShift.filtration F v) μ h t
        (MatrixFourierInput.input (DeterministicItoShift.filtration F v) μ h G hG hβ hβ1 V hV i a m))=
      StoppedItoInputs.stop F μ T (v+t) (MatrixFourierInput.input F μ T G hG hβ hβ1 U hU i a m)-
        StoppedItoInputs.stop F μ T v (MatrixFourierInput.input F μ T G hG hβ hβ1 U hU i a m) := by
  apply DeterministicWindowInput.stopped F μ T v h hvh
    (MatrixFourierInput.input F μ T G hG hβ hβ1 U hU i a m)
    (MatrixFourierInput.input (DeterministicItoShift.filtration F v) μ h G hG hβ hβ1 V hV i a m)
    (MatrixFourierInput.row T G hG hβ hβ1 U i a m)
    (MatrixFourierInput.row h G hG hβ hβ1 V i a m)
    (MatrixFourierInput.predictable _ h G hG hβ hβ1 V hV i a m)
    (MatrixFourierInput.input_ae F μ T G hG hβ hβ1 U hU i a m)
    (MatrixFourierInput.input_ae _ μ h G hG hβ hβ1 V hV i a m)
  intro s hs ω
  have hst : v+s≤T := (add_le_add le_rfl hs).trans hvh
  simp only [MatrixFourierInput.row,hState s hs ω,smul_smul,FourierHeatInput.multiplier]
  rw [min_eq_left (show (s : ℝ)≤h from hs),
    min_eq_left (show ((v+s : ℝ≥0) : ℝ)≤(T : ℝ) from by exact_mod_cast hst)]
  congr 1
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring
  exact ht

end SHEStochastic.MatrixFourierShiftInput
