module

public import SHEStochastic.ScalarLipschitzFourierMild

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzZeroEquation
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzConvolution
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (hM : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))

local notation "J" => FiniteCylindricalIto.terminalIto P.toCoordinates e

/-- Unstopped integrating-factor identity, on the original driver
with the original unbounded coefficient. -/
def Equation (u₀ : RealL2) : Prop :=
  ∀ (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0),t≤H →
    (J).integral (StoppedItoInputs.stop F μ H t
      (ScalarGrowingFourierInput.input F μ H U hU hg zero_lt_one le_rfl ψ n hM)) =ᵐ[μ]
      (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*φ ψ n (U t ω)-φ ψ n u₀)

theorem of_stopped (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
    (hc : ∀ ω,Continuous (fun t => U t ω)) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (hEq : ScalarStoppedMildMoment.Equation F μ H U hU hc hg zero_lt_one le_rfl J b (fun _ _ => 0) u₀) :
    Equation e P hg U hU hM u₀ := by
  intro ψ n t ht
  exact ScalarGrowingFourierInput.increment_primitive F μ H U hU hg zero_lt_one le_rfl ψ n
    P e hc hn b u₀ hEq hM t ht

theorem mild (u₀ : RealL2) (hEq : Equation e P hg U hU hM u₀)
    (t : ℝ≥0) (ht : t≤H) (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    U t=ᵐ[μ] fun ω => NativeHeatObservation.heat (t : ℝ) u₀+
      (ito e P).integral (input e hg U hU t hE) ω := by
  have hφ (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
      (fun ω => φ ψ n (U t ω)) =ᵐ[μ] fun ω =>
        φ ψ n (NativeHeatObservation.heat (t : ℝ) u₀+
          (ito e P).integral (input e hg U hU t hE) ω) := by
    filter_upwards [hEq ψ n t ht,ScalarLipschitzFourierMild.coordinate e P hg U hU hM t ht hE ψ n]
      with ω h₁ h₂
    rw [map_add,h₂,h₁,NativeFourierHeatCoordinate.coordinate_heat ψ n (t := (t : ℝ)) t.property,
      mul_sub,←mul_assoc,←Real.exp_add,show -(t : ℝ)*(n : ℝ)^2+(t : ℝ)*(n : ℝ)^2=0 by ring,
      Real.exp_zero,one_mul]
    ring
  filter_upwards [ae_all_iff.mpr (hφ Complex.reCLM),ae_all_iff.mpr (hφ Complex.imCLM)] with ω hr hi
  exact NativeFourierStateSeparation.ext hr hi

end SHEStochastic.ScalarLipschitzZeroEquation
