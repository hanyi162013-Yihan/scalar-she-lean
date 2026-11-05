module

public import SHEStochastic.MatrixUnboundedFourierInput
public import SHEStochastic.MatrixFourierShiftInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixUnboundedFourierShiftInput
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
    (G : EuclideanSpace ℝ d → Matrix d d ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (U V : ℝ≥0×Ω → Physical (d := d))
    (hU : StronglyMeasurable[F.predictable] U)
    (hV : StronglyMeasurable[(DeterministicItoShift.filtration F v).predictable] V)
    (hEnergyU : Integrable (fun p => ‖U p‖^2) (energyMeasure μ T))
    (hEnergyV : Integrable (fun p => ‖V p‖^2) (energyMeasure μ h))
    (hState : ∀ t,t≤h → ∀ ω,V (t,ω)=U (v+t,ω))

include hState in
/-- The literal unbounded matrix Fourier inputs paste across one
physical-time block with the same exponential integrating factor. -/
theorem stopped (i : d) (a : ℂ →L[ℝ] ℝ) (m : ℤ) (t : ℝ≥0) (ht : t≤h) :
    Real.exp ((v : ℝ)*(m : ℝ)^2) • DeterministicItoShift.input F μ T v h hvh
      (StoppedItoInputs.stop (DeterministicItoShift.filtration F v) μ h t
        (MatrixUnboundedFourierInput.input (DeterministicItoShift.filtration F v) μ h
          G hG hβ hβ1 V hV hEnergyV i a m)) =
      StoppedItoInputs.stop F μ T (v+t)
        (MatrixUnboundedFourierInput.input F μ T G hG hβ hβ1 U hU hEnergyU i a m)-
      StoppedItoInputs.stop F μ T v
        (MatrixUnboundedFourierInput.input F μ T G hG hβ hβ1 U hU hEnergyU i a m) := by
  apply DeterministicWindowInput.stopped F μ T v h hvh
    (MatrixUnboundedFourierInput.input F μ T G hG hβ hβ1 U hU hEnergyU i a m)
    (MatrixUnboundedFourierInput.input (DeterministicItoShift.filtration F v) μ h
      G hG hβ hβ1 V hV hEnergyV i a m)
    (MatrixUnboundedFourierInput.row T G hG hβ hβ1 U i a m)
    (MatrixUnboundedFourierInput.row h G hG hβ hβ1 V i a m)
    (MatrixUnboundedFourierInput.predictable _ h G hG hβ hβ1 V hV i a m)
    (MatrixUnboundedFourierInput.input_ae F μ T G hG hβ hβ1 U hU hEnergyU i a m)
    (MatrixUnboundedFourierInput.input_ae _ μ h G hG hβ hβ1 V hV hEnergyV i a m)
  intro s hs ω
  have hst : v+s≤T := (add_le_add le_rfl hs).trans hvh
  simp only [MatrixUnboundedFourierInput.row,hState s hs ω,smul_smul,FourierHeatInput.multiplier]
  rw [min_eq_left (show (s : ℝ)≤h from hs),
    min_eq_left (show ((v+s : ℝ≥0) : ℝ)≤(T : ℝ) from by exact_mod_cast hst)]
  congr 1
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring
  exact ht

end SHEStochastic.MatrixUnboundedFourierShiftInput
