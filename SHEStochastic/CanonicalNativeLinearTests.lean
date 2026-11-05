module

public import SHEStochastic.CanonicalLinearFluctuation
public import SHEStochastic.NativeFourierPathMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.CanonicalNativeLinearTests
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 StoppedPathPasting
open scoped NNReal ENNReal
variable {E A ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [Countable ι] [DecidableEq ι]
    (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ A)
    (W : ℝ≥0 → Ω → E) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (hcW : ∀ ω,Continuous (fun t => W t ω)) (L : E →L[ℝ] ℝ) (rate : ℝ)
    (r : Process (E := A) F μ H)
    (hRep : ∀ t,t ≤ H → (fun ω => Real.exp ((t : ℝ)*rate)*L (W t ω)-L (W 0 ω)) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (StoppedItoInputs.stop F μ H t r))
local notation "X" => CanonicalNativeBrownian.bundle F μ H P W hcW
local notation "M" => CanonicalLinearFluctuation.value (ι := ι) H L rate

include hRep in
theorem representation (t : ℝ≥0) : (M t ∘ X) =ᵐ[μ]
    (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H (min t H) r) := by
  filter_upwards [hRep (min t H) (min_le_right _ _)] with ω hω
  rw [Function.comp_apply,CanonicalLinearFluctuation.comp_bundle]
  exact hω

include hW hRep in
theorem subgaussian (B : ℝ≥0)
    (hb : ∀ᵐ p ∂FiniteScalarIto.inputMeasure F μ H,‖r p‖ ≤ B) (t : ℝ≥0) :
    HasSubgaussianMGF (M t) (min t H*B^2) (μ.map X) := by
  have hWa (t : ℝ≥0) : Measurable[F t] (W t) :=
    ((show IsStronglyPredictable F W from hW).stronglyAdapted t).measurable
  have hX := CanonicalNativeBrownian.measurable_bundle F μ H P W hcW hWa
  have hx := (CanonicalLinearFluctuation.continuous (ι := ι) H L rate t).measurable
  apply (HasSubgaussianMGF.id_map_iff hx.aemeasurable).mp
  rw [Measure.map_map hx hX]
  apply (HasSubgaussianMGF.id_map_iff (hx.comp hX).aemeasurable).mpr
  have hs := NativeBandMoments.increment_subgaussian P e r B hb
    (s := 0) (t := min t H) zero_le (min_le_right _ _)
  simp only [tsub_zero] at hs
  apply hs.congr
  filter_upwards [representation F μ H P e W hcW L rate r hRep t,Lp.coeFn_zero ℝ 2 μ] with ω hr hz
  rw [NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero,hz,Pi.zero_apply,sub_zero]
  exact hr.symm

include hW hRep in
/-- Native martingale identities transfer to the full joint canonical
law for any Hilbert state and linear integrating-factor coordinate. -/
theorem identity (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction (CanonicalLinearFluctuation.Space (E := E) (ι := ι) H) ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*(M t x-M s x) ∂μ.map X)=0 := by
  have hWa (t : ℝ≥0) : Measurable[F t] (W t) :=
    ((show IsStronglyPredictable F W from hW).stronglyAdapted t).measurable
  have hX := CanonicalNativeBrownian.measurable_bundle F μ H P W hcW hWa
  have hPast := CanonicalFutureStateDriver.adapted_past F W hcW P.W P.continuous hWa P.adapted
    0 H (CanonicalStateDriverFiltration.clock H s)
  change Measurable[F (0+(CanonicalStateDriverFiltration.clock H s).val.toNNReal)]
    (CanonicalStateDriverFiltration.history H s ∘ X) at hPast
  rw [CanonicalFourierFluctuation.clock_time H s,zero_add] at hPast
  obtain ⟨Y,_,_,_,hm,hr⟩ := NativeMartingaleVersion.exists_version P e hnull r
  have ht := ContinuousStoppedMartingaleTests.weighted_increment μ F Y hm
    (min s H) (min t H) (min_le_min_right _ hst)
    (fun ω => ψ (CanonicalStateDriverFiltration.history H s (X ω)))
    (ψ.continuous.measurable.comp hPast).stronglyMeasurable ‖ψ‖ (fun _ => ψ.norm_coe_le_norm _)
  rw [integral_map hX.aemeasurable]
  · have he : (fun ω => M t (X ω)-M s (X ω)) =ᵐ[μ]
        fun ω => Y (min t H) ω-Y (min s H) ω := by
      filter_upwards [representation F μ H P e W hcW L rate r hRep t,
        representation F μ H P e W hcW L rate r hRep s,hr (min t H),hr (min s H)] with ω hmt hms hyt hys
      exact congrArg₂ (fun a b : ℝ => a-b) (hmt.trans hyt.symm) (hms.trans hys.symm)
    exact (integral_congr_ae (he.mono fun ω hh => congrArg (fun z : ℝ => ψ (CanonicalStateDriverFiltration.history H s (X ω))*z) hh)).trans ht
  · exact ((ψ.continuous.comp (WeakLimitCanonicalBrownian.continuous_history H s)).mul
      ((CanonicalLinearFluctuation.continuous H L rate t).sub
        (CanonicalLinearFluctuation.continuous H L rate s))).stronglyMeasurable.aestronglyMeasurable

end SHEStochastic.CanonicalNativeLinearTests
