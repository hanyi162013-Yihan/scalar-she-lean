module

public import SHEStochastic.GlobalBoundedMildRecognition
public import SHEStochastic.GlobalBoundedFourierRecognition
public import SHEStochastic.BoundedFourierMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalBoundedFourierMartingale
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate BoundedFourierMartingale
open scoped NNReal ENNReal Topology

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖≤B) (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T:=2*Real.pi))))
  (ξ : Ω → RealL2) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := ⟨rfl⟩

/-- The actual bounded Fourier fluctuation is one native martingale
on the entire closed finite horizon. The convolution and its Fourier
identification are constructed from the source equation. -/
theorem exists_version (hH : 0<H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ sample, Continuous (M · sample)) ∧ StronglyAdapted F M ∧
      StronglyMeasurable[F.predictable] (Function.uncurry M) ∧ Martingale M F μ ∧
      (∀ t, M t=ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H t (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n))) ∧
      ∀ᵐ sample ∂μ, ∀ t : ℝ≥0, t≤H → fluctuation W ξ a n t sample=M t sample := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T:=2*Real.pi))) := e.repr.toHomeomorph.secondCountableTopology
  obtain ⟨Y,hm,he,_⟩ := GlobalBoundedHeatTightness.exists_tight_versions_varying F μ H
    (fun _ : ℕ ↦ physical W) (fun _ ↦ physical_predictable F W hW) (fun _ ↦ hG) hβ hβ1.le B
    (fun _ ↦ hb) (fun _ ↦ P) e
  have hclosed := GlobalBoundedMildRecognition.closed F μ H W hW hG hβ hβ1 B hb P e
    ξ hH hcW hnull hEquation (Y 0) (hm 0) (he 0)
  have hmild : GlobalBoundedFourierRecognition.HasClosedVersion F μ H W hW hG hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ := ⟨Y 0,hm 0,he 0,hclosed⟩
  have hf := GlobalBoundedFourierRecognition.fourier_of_closed F μ H W hW hG hβ hβ1 B hb hH
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ hmild
  obtain ⟨M,hcM,haM,hpM,hmM,hrM⟩ := NativeMartingaleVersion.exists_version P e hnull
    (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)
  refine ⟨M,hcM,haM,hpM,hmM,hrM,?_⟩
  have hfixed (T : ℝ≥0) (hTH : T≤H) : fluctuation W ξ a n T=ᵐ[μ] M T :=
    (hf T hTH a n).trans (hrM T).symm
  have hfc (sample : Ω) : Continuous (fun t : ℝ ↦ fluctuation W ξ a n t.toNNReal sample) :=
    ((Real.continuous_exp.comp (continuous_real_toNNReal.subtype_val.mul_const _)).mul
      ((coordinate a n).continuous.comp ((hcW sample).comp continuous_real_toNNReal))).sub continuous_const
  have hmc (sample : Ω) : Continuous (fun t : ℝ ↦ M t.toNNReal sample) :=
    (hcM sample).comp continuous_real_toNNReal
  have hh := AEContinuousIntervalClosure.ae_eq_Icc μ
    (fun t sample ↦ fluctuation W ξ a n t.toNNReal sample) (fun t sample ↦ M t.toNNReal sample)
    hfc hmc 0 H hH (fun t ht ↦ hfixed t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2.le))
  filter_upwards [hh] with sample hsample t ht
  simpa only [Real.toNNReal_coe] using hsample t ⟨t.property,ht⟩

include hb in
/-- All finite-horizon Fourier fluctuation moments are controlled by
the same bounded native row, without a moment assumption on ξ. -/
theorem subgaussian (hH : 0<H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (T : ℝ≥0) (hT : T≤H) : ProbabilityTheory.HasSubgaussianMGF (fluctuation W ξ a n T)
      (T*BoundedFourierInput.cap H B a n^2) μ := by
  obtain ⟨M,_,_,_,_,hr,he⟩ := exists_version F μ H W hW hG hβ hβ1 B hb P e ξ a n hH hcW hnull hEquation
  have hs := NativeBandMoments.increment_subgaussian P e
    (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)
    (BoundedFourierInput.cap H B a n) (BoundedFourierInput.input_bound F μ H W hW hG hβ hβ1 B hb a n)
    (s:=0) (t:=T) zero_le hT
  simp only [tsub_zero] at hs
  apply hs.congr
  filter_upwards [hr T,he,Lp.coeFn_zero ℝ 2 μ] with sample hr he hz
  rw [NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero,hz,Pi.zero_apply,sub_zero]
  exact hr.symm.trans (he T hT).symm

end SHEStochastic.GlobalBoundedFourierMartingale
