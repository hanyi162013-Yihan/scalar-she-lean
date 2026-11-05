module

public import SHEStochastic.ScalarStoppedHeatClock
public import SHEStochastic.ScalarStoppedMildMoment
public import SHEStochastic.FiniteCylindricalParameterVersions
public import Mathlib.Topology.Order.IsLUB

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedZeroEndpoint
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)
  (u₀ : RealL2)

local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁
local notation "S" => NativeHeatObservation.heat
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "τ" => ContinuousNormExit.exit W

/-- The actual stopped Fourier identities extend from the interior to
the closed deterministic horizon using the continuous prefix of the
same original stochastic heat row. -/
theorem closed (hH : 0<H) (hJ : ContinuousStoppedVersions J)
    (N : ℕ) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)
    (heq : ∀ t : ℝ≥0,t<H → ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<τ N ω →
      φ ψ n (W t ω-S (t : ℝ) u₀)=J.integral (v N t ψ n) ω) :
    ∀ t : ℝ≥0,t≤H → ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<τ N ω →
      φ ψ n (W t ω-S (t : ℝ) u₀)=J.integral (v N t ψ n) ω := by
  intro t ht
  rcases lt_or_eq_of_le ht with h | he
  · exact heq t h
  subst t
  obtain ⟨Z,hZ,hrep⟩ := hJ (v N H ψ n)
  obtain ⟨s,_,hs,hst⟩ := exists_seq_strictMono_tendsto' hH
  let k (r : ℝ≥0) := Real.exp (((H : ℝ)-(r : ℝ))*(n : ℝ)^2)
  have hI (r : ℝ≥0) (hr : r≤H) : J.integral (v N r ψ n) =ᵐ[μ] fun ω => k r*Z r ω := by
    rw [ScalarStoppedHeatClock.input_eq F μ H W hW hc hg hβ hβ₁ N ψ n r hr,map_smul]
    filter_upwards [hrep r,Lp.coeFn_smul (k r)
      (J.integral (StoppedItoInputs.stop F μ H r (v N H ψ n)))] with ω hrep hsm
    rw [hsm,Pi.smul_apply,smul_eq_mul,hrep]
  have htime : Continuous fun r : ℝ≥0 => S (r : ℝ) u₀ := by
    have hp : Continuous (fun r : ℝ≥0 => ((r : ℝ)/NativeHeatObservation.timeScale,u₀)) := by fun_prop
    change Continuous ((fun p : ℝ×RealL2 => (RealHeat.realHeat p.1) p.2) ∘
      fun r : ℝ≥0 => ((r : ℝ)/NativeHeatObservation.timeScale,u₀))
    exact RealHeat.continuous_realHeat_action.comp hp
  have hke : Continuous k := by unfold k; fun_prop
  filter_upwards [ae_all_iff.mpr (fun m => heq (s m) (hs m).2),
    ae_all_iff.mpr (fun m => hI (s m) (hs m).2.le),hI H le_rfl] with ω hEq hZs hZH hω
  rw [hZH]
  have hl : Tendsto (fun m => φ ψ n (W (s m) ω-S (s m : ℝ) u₀)) atTop
      (𝓝 (φ ψ n (W H ω-S (H : ℝ) u₀))) :=
    ((φ ψ n).continuous.comp ((hc ω).sub htime)).continuousAt.tendsto.comp hst
  have hr : Tendsto (fun m => k (s m)*Z (s m) ω) atTop (𝓝 (k H*Z H ω)) :=
    (hke.mul (hZ ω)).continuousAt.tendsto.comp hst
  refine tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun m => ?_))
  exact ((hEq m) ((WithTop.coe_le_coe.mpr (hs m).2.le).trans_lt hω)).trans (hZs m) |>.symm

end SHEStochastic.ScalarStoppedZeroEndpoint
