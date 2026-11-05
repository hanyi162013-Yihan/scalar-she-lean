module

public import SHEStochastic.ScalarStoppedFourierLocality
public import SHEStochastic.ScalarStoppedMildMoment
public import SHEStochastic.ScalarStoppedDriftAlgebra
public import SHEStochastic.GlobalBoundedFourierRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedBoundedBridge
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
  (B : ℝ≥0) (hB : ∀ z,‖g z‖≤B)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ Noise)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)

local notation "J" => FiniteCylindricalIto.terminalIto P.toCoordinates e
local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁.le
local notation "w" => BoundedFourierInput.input F μ H W hW hg hβ hβ₁ B hB
local notation "S" => NativeHeatObservation.heat
local notation "φ" => NativeFourierHeatCoordinate.coordinate

/-- For bounded diffusion the actual stopped zero-drift equation and
the global native Fourier mild equation have the same continuous states. -/
theorem iff_bounded (hn : NullCompleteFiltration.ContainsNullSets F μ) :
    ScalarStoppedMildMoment.Equation F μ H W hW hc hg hβ hβ₁.le J b (fun _ _ => 0) u₀ ↔
      GlobalBoundedFourierRecognition.FourierEquation F μ H W hW hg hβ hβ₁ B hB J (fun _ => u₀) := by
  have hComp (N : ℕ) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t≤H) :=
    ScalarStoppedFourierLocality.compare F μ H W hW hc hg hβ hβ₁.le N ψ n P e hn (w ψ n)
      ((BoundedFourierInput.input_ae F μ H W hW hg hβ hβ₁ B hB ψ n).mono (fun _ h _ => h)) t ht
  have hHeat (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) : φ ψ n (S (t : ℝ) u₀) =
      Real.exp (-(t : ℝ)*(n : ℝ)^2)*φ ψ n u₀ :=
    NativeFourierHeatCoordinate.coordinate_heat ψ n t.property u₀
  have hk (t : ℝ≥0) (n : ℤ) :
      Real.exp ((t : ℝ)*(n : ℝ)^2)*Real.exp (-(t : ℝ)*(n : ℝ)^2)=1 := by
    rw [←Real.exp_add,show (t : ℝ)*(n : ℝ)^2+(-(t : ℝ))*(n : ℝ)^2=0 by ring,Real.exp_zero]
  constructor
  · intro he t ht ψ n
    filter_upwards [ae_all_iff.mpr (fun N => he N t ht ψ n),
      ae_all_iff.mpr (fun N => hComp N ψ n t ht)] with ω he hC
    have htop := ContinuousNormExit.tendsto_top W hc ω
    rw [WithTop.tendsto_nhds_top_iff] at htop
    obtain ⟨N,hN⟩ := (htop t).exists
    have h := he N hN
    rw [ScalarStoppedDriftAlgebra.zero,sub_zero,map_sub,hHeat, hC N hN] at h
    have hh := congrArg (fun x : ℝ => Real.exp ((t : ℝ)*(n : ℝ)^2)*x) h
    simp only [mul_sub,←mul_assoc,hk,one_mul] at hh
    exact hh
  · intro he N t ht ψ n
    filter_upwards [he t ht ψ n,hComp N ψ n t ht] with ω h hC hN
    rw [ScalarStoppedDriftAlgebra.zero,sub_zero,map_sub,hHeat,hC hN]
    have hh := congrArg (fun x : ℝ => Real.exp (-(t : ℝ)*(n : ℝ)^2)*x) h
    change Real.exp (-(t : ℝ)*(n : ℝ)^2)*
      (Real.exp ((t : ℝ)*(n : ℝ)^2)*φ ψ n (W t ω)-φ ψ n u₀) =
      Real.exp (-(t : ℝ)*(n : ℝ)^2)*(J).integral (StoppedItoInputs.stop F μ H t (w ψ n)) ω at hh
    rwa [mul_sub,←mul_assoc,mul_comm (Real.exp (-(t : ℝ)*(n : ℝ)^2)),hk,one_mul] at hh

end SHEStochastic.ScalarStoppedBoundedBridge
