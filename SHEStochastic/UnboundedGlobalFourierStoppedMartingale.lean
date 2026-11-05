module

public import SHEStochastic.UnboundedGlobalFourierEquation
public import SHEStochastic.UnboundedFourierStoppedMartingale
public import SHEStochastic.UnboundedNativeMildRecognition
public import SHEStochastic.ContinuousEqualityBeforeExit
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedGlobalFourierStoppedMartingale
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation UnboundedFourierStoppedMartingale
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  {ι : Type*} [Countable ι] [DecidableEq ι]
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)

/-- The actual Fourier mode, stopped at the actual L2 exit and the
full horizon, is a martingale including the terminal endpoint. -/
theorem martingale (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (stoppedProcess (fluctuation W u₀ a n)
      (fun ω ↦ min (H : WithTop ℝ≥0) (exit W N ω))) F μ := by
  obtain ⟨M, hcM, _, _, hm, hr, hlocal⟩ := UnboundedGlobalFourierEquation.exists_martingale
    F μ H hH W hW hG hβ hβ1 P e u₀ hcW hnull hEquation N a n
  have hzero : fluctuation W u₀ a n 0 =ᵐ[μ] M 0 := by
    have hm0 := hr 0
    rw [NNReal.coe_zero, StoppedItoInputs.stop_zero, map_zero] at hm0
    filter_upwards [UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull
      (UnboundedGlobalNativeEquation.to_local F μ H W hW hG hβ hβ1 P e (fun _ ↦ u₀) hEquation),
      hm0, Lp.coeFn_zero ℝ 2 μ] with ω hx hm hz
    simp only [fluctuation, NNReal.coe_zero, zero_mul, Real.exp_zero, one_mul, hx, sub_self]
    exact (hm.trans hz).symm
  exact of_representation F μ W hW u₀ H hcW hnull N a n M hcM hm hzero hlocal

end SHEStochastic.UnboundedGlobalFourierStoppedMartingale
