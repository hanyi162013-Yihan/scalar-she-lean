module

public import SHE.BoundedStoppedMoments
public import SHE.HaarContinuousVersion
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.BoundedStoppedVersion
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (I : StandardTerminalIto (C := C) (E := E) 𝓕 μ H)
variable (u : Process (E := C) 𝓕 μ H)

def process (r : ℝ) (ω : Ω) : E :=
  I.integral (stop 𝓕 μ H (HaarUnitTimeMoments.clock H r) u) ω

theorem process_measurable (r : ℝ) : Measurable (process 𝓕 μ H I u r) :=
  (Lp.stronglyMeasurable _).measurable

theorem increment_moment16 (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {K : ℝ} (hK : 0≤K) (hu : ∀ᵐ p ∂energyMeasure μ H, ‖u p‖^2≤K)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    (∫⁻ ω,ENNReal.ofReal (‖process 𝓕 μ H I u s ω-process 𝓕 μ H I u t ω‖^16) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*K^8*|s-t|^2) := by
  have hb := BoundedStoppedMoments.increment 𝓕 μ H hH I B hBDG u hK hu
    (HaarUnitTimeMoments.clock H s) (HaarUnitTimeMoments.clock H t)
    (HaarUnitTimeMoments.clock_bound H s) (HaarUnitTimeMoments.clock_bound H t)
  have hd : ((HaarUnitTimeMoments.clock H s:ℝ)-(HaarUnitTimeMoments.clock H t:ℝ))^2≤|s-t|^2 := by
    rw [HaarUnitTimeMoments.clock_coe H hs,HaarUnitTimeMoments.clock_coe H ht,←mul_sub,mul_pow,sq_abs]
    have hH2 : (H:ℝ)^2≤1 := by nlinarith [H.2]
    exact (mul_le_mul_of_nonneg_right hH2 (sq_nonneg (s-t))).trans_eq (one_mul _)
  exact hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd (by positivity)))

/-- An actual continuous modification of the original stopped integral.
It is constructed by the already proved Kolmogorov theorem, so continuity
is not an additional stochastic input. -/
def version (t : ℝ≥0) (ω : Ω) : E :=
  KolmogorovModification.modification (process 𝓕 μ H I u) (HaarContinuousVersion.normalizedTime H t) ω

theorem continuous_version (hH0 : 0<H) (ω : Ω) :
    Continuous (fun t => version 𝓕 μ H I u t ω) :=
  (KolmogorovModification.continuousOn_modification (process 𝓕 μ H I u) ω).comp_continuous
    (HaarContinuousVersion.continuous_normalizedTime H) (HaarContinuousVersion.normalizedTime_mem hH0)

theorem version_ae (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {K : ℝ} (hK : 0≤K) (hu : ∀ᵐ p ∂energyMeasure μ H, ‖u p‖^2≤K) (t : ℝ≥0) :
    version 𝓕 μ H I u t =ᵐ[μ] I.integral (stop 𝓕 μ H (min t H) u) := by
  have he := KolmogorovModification.modification_ae μ (process 𝓕 μ H I u)
    (fun r _ => process_measurable 𝓕 μ H I u r) (by positivity : 0≤(B:ℝ)*K^8)
    (fun s hs t ht => increment_moment16 𝓕 μ H I u hH B hBDG hK hu hs ht)
    (HaarContinuousVersion.normalizedTime_mem hH0 t)
  filter_upwards [he] with ω hω
  change KolmogorovModification.modification (process 𝓕 μ H I u)
    (HaarContinuousVersion.normalizedTime H t) ω =
      I.integral (stop 𝓕 μ H (HaarUnitTimeMoments.clock H
        (HaarContinuousVersion.normalizedTime H t)) u) ω at hω
  rw [HaarContinuousVersion.clock_normalizedTime hH0 t] at hω
  exact hω

theorem predictable_version (hH : (H:ℝ)≤1) (hH0 : 0<H)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {K : ℝ} (hK : 0≤K) (hu : ∀ᵐ p ∂energyMeasure μ H, ‖u p‖^2≤K) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (version 𝓕 μ H I u)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
  · intro t
    obtain ⟨Z,hZ,he⟩ := I.adapted t (stop 𝓕 μ H (min t H) u) (by
      filter_upwards [stop_stopped 𝓕 μ H (min t H) u] with p hp htp
      exact hp (lt_of_le_of_lt (min_le_left t H) htp))
    exact ⟨Z,hZ,(version_ae 𝓕 μ H I u hH hH0 B hBDG hK hu t).trans he⟩
  · exact continuous_version 𝓕 μ H I u hH0

end SHE.BoundedStoppedVersion
