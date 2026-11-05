module

public import SHEStochastic.UnboundedNativeFourierEquation
public import SHEStochastic.UnboundedNativeMildRecognition
public import SHEStochastic.ContinuousEqualityBeforeExit
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.UnboundedFourierStoppedMartingale
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation
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

def fluctuation (W : ℝ≥0 → Ω → RealL2) (u₀ : RealL2)
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((t : ℝ) * (n : ℝ) ^ 2) * NativeFourierHeatCoordinate.coordinate a n (W t ω) -
    NativeFourierHeatCoordinate.coordinate a n u₀

def clock (H : ℝ≥0) (W : ℝ≥0 → Ω → RealL2) (N : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min ((min H 1 : ℝ≥0) : WithTop ℝ≥0) (exit W N ω)

include hW in
/-- A continuous native representative identifies the original stopped
Fourier mode on any closed horizon. Shared by local and global recognition. -/
theorem of_representation (K : ℝ≥0) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (M : ℝ≥0 → Ω → ℝ)
    (hcM : ∀ ω, Continuous (M · ω)) (hm : Martingale M F μ)
    (hzero : fluctuation W u₀ a n 0 =ᵐ[μ] M 0)
    (hlocal : ∀ t : ℝ≥0, t < K → ∀ᵐ ω ∂μ,
      (t : WithTop ℝ≥0) < exit W N ω → fluctuation W u₀ a n t ω = M t ω) :
    Martingale (stoppedProcess (fluctuation W u₀ a n)
      (fun ω ↦ min (K : WithTop ℝ≥0) (exit W N ω))) F μ := by
  let τ : Ω → WithTop ℝ≥0 := fun ω ↦ min (K : WithTop ℝ≥0) (exit W N ω)
  let r (ω : Ω) : ℝ≥0 := (τ ω).untopA
  have hne (ω : Ω) : τ ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hcast : (fun ω ↦ (r ω : WithTop ℝ≥0)) = τ := by
    funext ω
    change ((τ ω).untopA : WithTop ℝ≥0) = τ ω
    rw [WithTop.untopA_eq_untop (hne ω), WithTop.coe_untop]
  have hcX (ω : Ω) : Continuous (fun t ↦ fluctuation W u₀ a n t ω) :=
    ((Real.continuous_exp.comp (continuous_subtype_val.mul_const _)).mul
      ((NativeFourierHeatCoordinate.coordinate a n).continuous.comp (hcW ω))).sub continuous_const
  have he (t : ℝ≥0) : ∀ᵐ ω ∂μ, t < r ω → fluctuation W u₀ a n t ω = M t ω := by
    by_cases hTK : t < K
    · filter_upwards [hlocal t hTK] with ω hω ht
      exact hω (((WithTop.lt_untopA_iff (hne ω)).mp ht).trans_le (min_le_right _ _))
    · exact Eventually.of_forall fun ω ht ↦
        (hTK (WithTop.coe_lt_coe.mp
          (((WithTop.lt_untopA_iff (hne ω)).mp ht).trans_le (min_le_left _ _)))).elim
  have heq := ContinuousEqualityBeforeExit.stopped_eq μ (fluctuation W u₀ a n) M r
    (Eventually.of_forall hcX) (Eventually.of_forall hcM) hzero he
  rw [hcast] at heq
  have hτ : IsStoppingTime F τ :=
    (isStoppingTime_const F K).min (exit_stopping F W hW hcW N)
  have hMs := hm.stoppedProcess (fun ω t ↦ (hcM ω).continuousAt.continuousWithinAt) hτ
  have ha : StronglyAdapted F (stoppedProcess (fluctuation W u₀ a n) τ) := fun t ↦
    NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t (hMs.stronglyAdapted t)
      (heq.mono fun ω hω ↦ hω t)
  exact hMs.congr ha (fun t ↦ heq.mono fun ω hω ↦ (hω t).symm)

/-- The actual original Fourier fluctuation, stopped at an L2 exit
and the closed initial horizon, is a genuine martingale. Continuity
handles the random exit and terminal endpoint on one common event. -/
theorem martingale (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
    (N : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (stoppedProcess (fluctuation W u₀ a n) (clock H W N)) F μ := by
  obtain ⟨M, hcM, _, _, hm, hr, hlocal⟩ := UnboundedNativeFourierEquation.exists_martingale
    F μ H W hW hG hβ hβ1 P e u₀ hcW hnull hEquation N a n
  have hzero : fluctuation W u₀ a n 0 =ᵐ[μ] M 0 := by
    have hm0 := hr 0
    rw [NNReal.coe_zero, StoppedItoInputs.stop_zero, map_zero] at hm0
    filter_upwards [UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation,
      hm0, Lp.coeFn_zero ℝ 2 μ] with ω hx hm hz
    simp only [fluctuation, NNReal.coe_zero, zero_mul, Real.exp_zero, one_mul, hx, sub_self]
    exact (hm.trans hz).symm
  exact of_representation F μ W hW u₀ (min H 1) hcW hnull N a n M hcM hm hzero
    (fun t ht ↦ hlocal t (ht.trans_le (min_le_left _ _))
      (show (t : ℝ) < 1 from ht.trans_le (min_le_right _ _)))

end SHEStochastic.UnboundedFourierStoppedMartingale
