module

public import SHEStochastic.ScalarStoppedFourierLocality
public import SHEStochastic.ScalarStoppedMomentUniform
public import SHEStochastic.ScalarStoppedDriftAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGrowingFourierInput
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)

local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "k" => NativeFourierHeatCoordinate.weight ψ n

/-- The original non-stopped integrating-factor mode. -/
def row (p : ℝ≥0×Ω) : Noise :=
  FourierHeatInput.multiplier H n p • StateNoiseCovariance.row ν hβ hβ₁ hg k (physical W p)

include hW in
theorem predictable : StronglyMeasurable[F.predictable] (row H W hg hβ hβ₁ ψ n) :=
  (FourierHeatInput.multiplier_measurable F H n).smul
    ((StateNoiseCovariance.row_continuous ν hβ hβ₁ hg k).comp_stronglyMeasurable
      (physical_predictable F W hW))

include hW in
theorem memLp (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H)) :
    @MemLp _ _ F.predictable _ _ (row H W hg hβ hβ₁ ψ n) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hm := predictable F H W hW hg hβ hβ₁ ψ n
  have ha := (hm.mono (predictable_le_product F)).aestronglyMeasurable (μ := energyMeasure μ H)
  let K := Real.exp ((H : ℝ)*(n : ℝ)^2)^2*(‖k‖^2*(4*(‖g 0‖+(C : ℝ))^2))
  let _ : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  have hi : Integrable (fun p => ‖row H W hg hβ hβ₁ ψ n p‖^2) (energyMeasure μ H) := by
    apply (((integrable_const (1 : ℝ)).add hM).const_mul K).mono' (ha.norm.pow 2)
    apply ae_of_all _
    intro p
    change ‖‖row H W hg hβ hβ₁ ψ n p‖^2‖ ≤ K*(1+‖W p.1 p.2‖^2)
    rw [Real.norm_of_nonneg (sq_nonneg _),row,norm_smul,mul_pow,Real.norm_eq_abs]
    have h := HolderCoefficientEnergyGrowth.row_bound ν hg hβ hβ₁ k (physical W p)
    rw [physical,LinearIsometry.norm_map] at h
    have hmul := pow_le_pow_left₀ (abs_nonneg _) (FourierHeatInput.multiplier_bound H n p) 2
    calc
      _ ≤ _ := mul_le_mul hmul h (sq_nonneg _) (sq_nonneg _)
      _ = _ := by dsimp [K]; ring
  have h := (memLp_two_iff_integrable_sq_norm ha).mpr hi
  exact (eLpNorm_trim (predictable_le_product F) hm).trans_lt h

def input (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H)) :
    Process (E := Noise) F μ H :=
  (memLp F μ H W hW hg hβ hβ₁ ψ n hM).toLp (row H W hg hβ hβ₁ ψ n)

theorem input_ae (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H)) :
    input F μ H W hW hg hβ hβ₁ ψ n hM =ᵐ[energyMeasure μ H] row H W hg hβ hβ₁ ψ n :=
  ae_eq_of_ae_eq_trim (memLp F μ H W hW hg hβ hβ₁ ψ n hM).coeFn_toLp

/-- At zero drift, the integrating-factor martingale is an explicit
function of the actual state at its observation time. -/
theorem increment_primitive {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ Noise)
    (hc : ∀ ω,Continuous (fun t => W t ω)) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
    (hEq : ScalarStoppedMildMoment.Equation F μ H W hW hc hg hβ hβ₁
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) b (fun _ _ => 0) u₀)
    (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H))
    (t : ℝ≥0) (ht : t≤H) :
    (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t (input F μ H W hW hg hβ hβ₁ ψ n hM)) =ᵐ[μ]
      (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*φ ψ n (W t ω)-φ ψ n u₀) := by
  have hC (N : ℕ) := ScalarStoppedFourierLocality.compare F μ H W hW hc hg hβ hβ₁ N ψ n P e hn
    (input F μ H W hW hg hβ hβ₁ ψ n hM)
    ((input_ae F μ H W hW hg hβ hβ₁ ψ n hM).mono (fun _ h _ => h)) t ht
  filter_upwards [ae_all_iff.mpr (fun N => hEq N t ht ψ n),ae_all_iff.mpr hC] with ω hEq hC
  have htop := ContinuousNormExit.tendsto_top W hc ω
  rw [WithTop.tendsto_nhds_top_iff] at htop
  obtain ⟨N,hN⟩ := (htop t).exists
  have h := hEq N hN
  rw [ScalarStoppedDriftAlgebra.zero,sub_zero,map_sub,
    NativeFourierHeatCoordinate.coordinate_heat ψ n (t := (t : ℝ)) t.property,hC N hN] at h
  have h₁ : Real.exp ((t : ℝ)*(n : ℝ)^2)*Real.exp (-(t : ℝ)*(n : ℝ)^2)=1 := by
    rw [←Real.exp_add,show (t : ℝ)*(n : ℝ)^2+(-(t : ℝ))*(n : ℝ)^2=0 by ring,Real.exp_zero]
  have hh := congrArg (fun z : ℝ => Real.exp ((t : ℝ)*(n : ℝ)^2)*z) h
  simp only [mul_sub,←mul_assoc,h₁,one_mul] at hh
  exact hh.symm

end SHEStochastic.ScalarGrowingFourierInput
