module

public import SHEStochastic.ScalarLipschitzConvolution
public import SHEStochastic.ScalarCanonicalObservation

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzFourierMild
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzHeatColumn ScalarLipschitzHeatColumns ScalarLipschitzKernelBounds ScalarLipschitzConvolution
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "w" => NativeFourierHeatCoordinate.weight
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

local notation "J" => FiniteCylindricalIto.terminalIto P.toCoordinates e
local notation "Col" => HilbertColumns.Space I RealL2
local notation "q" => (energyMeasure μ H).trim (predictable_le_product F)

theorem coordinate (hM : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))
    (t : ℝ≥0) (ht : t≤H) (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H))
    (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    (fun ω => φ ψ n ((ito e P).integral (input e hg U hU t hE) ω)) =ᵐ[μ] fun ω =>
      Real.exp (-(t : ℝ)*(n : ℝ)^2)*(J).integral
        (StoppedItoInputs.stop F μ H t
          (ScalarGrowingFourierInput.input F μ H U hU hg zero_lt_one le_rfl ψ n hM)) ω := by
  let u := input e hg U hU t hE
  let f := ScalarGrowingFourierInput.input F μ H U hU hg zero_lt_one le_rfl ψ n hM
  let d := Real.exp (-(t : ℝ)*(n : ℝ)^2)
  let : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  let v : Process (E := HilbertColumns.Space I ℝ) F μ H :=
    ((HilbertColumns.mapCLM (φ ψ n)).compLpL 2 q) u
  have hv :
      NoiseRestrictionBounds.input e.repr.symm.toLinearIsometry v=d • StoppedItoInputs.stop F μ H t f := by
    apply PastItoAlgebra.eq_of_ambient_ae F μ H
    filter_upwards [ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim e.repr.symm.toLinearIsometry v),
      ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (φ ψ n)).coeFn_compLpL u),
      input_ae e hg U hU t hE,ScalarGrowingFourierInput.input_ae F μ H U hU hg zero_lt_one le_rfl ψ n hM,
      StoppedItoInputs.stop_ae F μ H t f,
      ae_eq_of_ae_eq_trim (Lp.coeFn_smul d (StoppedItoInputs.stop F μ H t f))] with p h₁ h₂ h₃ h₄ h₅ h₆
    change v p=(HilbertColumns.mapCLM (φ ψ n)) (u p) at h₂
    rw [h₁,h₂,h₃,h₆,Pi.smul_apply,h₅]
    change e.repr.symm ((HilbertColumns.mapCLM (φ ψ n)) (raw e hg U t p)) = _
    rw [raw_row e hg U t p ψ n]
    by_cases hp : p.1<t
    · have hp' : p∈StoppedItoInputs.before (Ω := Ω) (t : ℝ) := by
        exact_mod_cast hp
      rw [ite_eq_left hp,indicator_of_mem hp',h₄,ScalarGrowingFourierInput.row,smul_smul]
      dsimp only [d,FourierHeatInput.multiplier]
      have hmin : min (p.1 : ℝ) (H : ℝ)=(p.1 : ℝ) :=
        min_eq_left (by exact_mod_cast hp.le.trans ht)
      rw [hmin,←Real.exp_add]
      congr 2
      ring
    · have hp' : p∉StoppedItoInputs.before (Ω := Ω) (t : ℝ) := by
        intro h
        exact hp (by exact_mod_cast (show (p.1 : ℝ)<t from h))
      rw [ite_eq_right hp,indicator_of_notMem hp',zero_smul,smul_zero]
  have hI : (φ ψ n).compLpL 2 μ ((ito e P).integral u) =
      d • (J).integral (StoppedItoInputs.stop F μ H t f) := by
    rw [show (ito e P).integral u = HilbertTerminalIto.integral F μ H
      (NativeNoiseEquivalence.basis NativePhysicalState.equivalence e)
      (restrictNoise J e.repr.symm.toLinearIsometry) u from rfl,HilbertTerminalIto.commutes]
    change (J).integral (NoiseRestrictionBounds.input e.repr.symm.toLinearIsometry v) = _
    rw [hv,map_smul]
  have he := (φ ψ n).coeFn_compLpL ((ito e P).integral u)
  rw [hI] at he
  filter_upwards [he,Lp.coeFn_smul d ((J).integral (StoppedItoInputs.stop F μ H t f))] with ω h₁ h₂
  exact h₁.symm.trans h₂

/-- A fixed point of the true Hilbert convolution solves every stopped
Fourier equation, including the endpoint of the full time horizon. -/
theorem stopped (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
    (hc : ∀ ω,Continuous (fun t => U t ω)) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (hM : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))
    (hE : ∀ t, t≤H → Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H))
    (hfix : ∀ t (ht : t≤H),U t=ᵐ[μ] fun ω =>
      NativeHeatObservation.heat (t : ℝ) u₀+(ito e P).integral (input e hg U hU t (hE t ht)) ω) :
    ScalarStoppedMildMoment.Equation F μ H U hU hc hg zero_lt_one le_rfl J b (fun _ _ => 0) u₀ := by
  intro N t ht ψ n
  let f := ScalarGrowingFourierInput.input F μ H U hU hg zero_lt_one le_rfl ψ n hM
  have hlocal := ScalarStoppedFourierLocality.compare F μ H U hU hc hg zero_lt_one le_rfl N ψ n P e hn
    f ((ScalarGrowingFourierInput.input_ae F μ H U hU hg zero_lt_one le_rfl ψ n hM).mono
      (fun _ h _ => h)) t ht
  filter_upwards [hfix t ht,coordinate e P hg U hU hM t ht (hE t ht) ψ n,hlocal] with ω hf hφ hl hω
  rw [ScalarStoppedDriftAlgebra.zero,sub_zero,hf,add_sub_cancel_left]
  exact hφ.trans (hl hω).symm

/-- Every zero-drift weak solution agrees with the Hilbert convolution
at each time for which the genuine Hilbert input is square integrable. -/
theorem from_stopped (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
    (hc : ∀ ω,Continuous (fun t => U t ω)) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (hM : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H))
    (hEq : ScalarStoppedMildMoment.Equation F μ H U hU hc hg zero_lt_one le_rfl J b (fun _ _ => 0) u₀)
    (t : ℝ≥0) (ht : t≤H) (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    U t=ᵐ[μ] fun ω => NativeHeatObservation.heat (t : ℝ) u₀+
      (ito e P).integral (input e hg U hU t hE) ω := by
  have hφ (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
      (fun ω => φ ψ n (U t ω)) =ᵐ[μ] fun ω =>
        φ ψ n (NativeHeatObservation.heat (t : ℝ) u₀+
          (ito e P).integral (input e hg U hU t hE) ω) := by
    have he := ScalarGrowingFourierInput.increment_primitive F μ H U hU hg zero_lt_one le_rfl ψ n
      P e hc hn b u₀ hEq hM t ht
    filter_upwards [he,coordinate e P hg U hU hM t ht hE ψ n] with ω h₁ h₂
    rw [map_add,h₂,h₁,NativeFourierHeatCoordinate.coordinate_heat ψ n (t := (t : ℝ)) t.property,mul_sub,←mul_assoc,
      ←Real.exp_add,show -(t : ℝ)*(n : ℝ)^2+(t : ℝ)*(n : ℝ)^2=0 by ring,Real.exp_zero,one_mul]
    ring
  filter_upwards [ae_all_iff.mpr (hφ Complex.reCLM),ae_all_iff.mpr (hφ Complex.imCLM)] with ω hr hi
  exact NativeFourierStateSeparation.ext hr hi

end SHEStochastic.ScalarLipschitzFourierMild
