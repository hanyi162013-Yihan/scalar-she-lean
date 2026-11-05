module

public import SHEStochastic.BoundedFourierInput
public import SHEStochastic.AEContinuousIntervalClosure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.BoundedFourierMartingale
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
  (ξ : Ω → RealL2) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

def fluctuation (t : ℝ≥0) (sample : Ω) : ℝ :=
  Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate a n (W t sample)-coordinate a n (ξ sample)

/-- A bounded coefficient makes the original Fourier fluctuation a
single native integral on the closed short horizon. The localized
equation is removed by actual L2 exits, not by a new solution assumption. -/
theorem exists_version (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (fun t ↦ M t sample)) ∧
      StronglyAdapted F M ∧ StronglyMeasurable[F.predictable] (Function.uncurry M) ∧
      Martingale M F μ ∧
      (∀ t, M t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H t (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n))) ∧
      ∀ᵐ sample ∂μ, ∀ t : ℝ≥0, t ≤ min H 1 → fluctuation W ξ a n t sample = M t sample := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let r := BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n
  obtain ⟨M, hcM, haM, hpM, hmM, hrM⟩ := NativeMartingaleVersion.exists_version P e hnull r
  refine ⟨M, hcM, haM, hpM, hmM, hrM, ?_⟩
  have hfixed (T : ℝ≥0) (hTH : T < H) (hT : (T : ℝ) < 1) :
      fluctuation W ξ a n T =ᵐ[μ] M T := by
    have hN (N : ℕ) : ∀ᵐ sample ∂μ, (T : WithTop ℝ≥0) < exit W N sample →
        fluctuation W ξ a n T sample = M T sample := by
      filter_upwards [UnboundedNativeFourierEquation.integrating_factor_random
        F μ H W hW hG hβ hβ1 P e ξ hcW hEquation N a n T hTH hT,
        BoundedFourierInput.integral_agrees F μ H W hW hG hβ hβ1 B hb a n P e hnull hcW N T,
        hrM T] with sample hlocal heq hrep hBefore
      exact (hlocal hBefore).trans ((heq hBefore.le).trans hrep.symm)
    filter_upwards [ae_all_iff.mpr hN] with sample hsample
    have ht := ContinuousNormExit.tendsto_top (fun t sample ↦ physical W (t, sample))
      (physical_continuous W hcW) sample
    rw [WithTop.tendsto_nhds_top_iff] at ht
    obtain ⟨N, hN⟩ := (ht T).exists
    exact hsample N hN
  have hf (sample : Ω) : Continuous (fun t : ℝ ↦ fluctuation W ξ a n t.toNNReal sample) :=
    ((Real.continuous_exp.comp (continuous_real_toNNReal.subtype_val.mul_const _)).mul
      ((coordinate a n).continuous.comp ((hcW sample).comp continuous_real_toNNReal))).sub continuous_const
  have hg (sample : Ω) : Continuous (fun t : ℝ ↦ M t.toNNReal sample) :=
    (hcM sample).comp continuous_real_toNNReal
  have hh := AEContinuousIntervalClosure.ae_eq_Icc μ
    (fun t sample ↦ fluctuation W ξ a n t.toNNReal sample) (fun t sample ↦ M t.toNNReal sample)
    hf hg 0 (min H 1) (by exact_mod_cast lt_min hH (by norm_num : (0 : ℝ≥0) < 1)) (by
      intro t ht
      have hT : t.toNNReal < min H 1 := by
        exact (Real.toNNReal_lt_iff_lt_coe ht.1).mpr ht.2
      exact hfixed t.toNNReal (hT.trans_le (min_le_left _ _))
        (by exact_mod_cast hT.trans_le (min_le_right _ _)))
  filter_upwards [hh] with sample hsample t ht
  simpa only [Real.toNNReal_coe] using hsample t ⟨t.property, by exact_mod_cast ht⟩

include hb in
/-- Every original Fourier fluctuation has the same sub-Gaussian
control, uniformly over coefficients with the same bound. Random L2
initial data cancel exactly in the fluctuation. -/
theorem subgaussian (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (T : ℝ≥0) (hT : T ≤ min H 1) :
    ProbabilityTheory.HasSubgaussianMGF (fluctuation W ξ a n T)
      (T * BoundedFourierInput.cap H B a n ^ 2) μ := by
  obtain ⟨M, _, _, _, _, hr, he⟩ := exists_version F μ H W hW hG hβ hβ1 B hb P e ξ a n
    hH hcW hnull hEquation
  have hs := NativeBandMoments.increment_subgaussian P e
    (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)
    (BoundedFourierInput.cap H B a n) (BoundedFourierInput.input_bound F μ H W hW hG hβ hβ1 B hb a n)
    (s := 0) (t := T) zero_le (hT.trans (min_le_left _ _))
  simp only [tsub_zero] at hs
  apply hs.congr
  filter_upwards [hr T, he, Lp.coeFn_zero ℝ 2 μ] with sample hr he hz
  rw [NNReal.coe_zero, StoppedItoInputs.stop_zero, map_zero, hz, Pi.zero_apply, sub_zero]
  exact hr.symm.trans (he T hT).symm

end SHEStochastic.BoundedFourierMartingale
