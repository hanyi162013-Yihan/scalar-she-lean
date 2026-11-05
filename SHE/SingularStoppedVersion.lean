module

public import SHE.SingularStoppedMoments
public import SHE.HaarContinuousVersion
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.SingularStoppedVersion
open Set MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H b : ℝ≥0) (I : StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)
variable (u : Process (E:=C) 𝓕 μ H)

def process (r : ℝ) (ω : Ω) : E :=
  I.integral (stop 𝓕 μ H (HaarUnitTimeMoments.clock b r) u) ω

theorem process_measurable (r : ℝ) : Measurable (process 𝓕 μ H b I u r) :=
  (Lp.stronglyMeasurable _).measurable

theorem increment_moment16 (hbH : b≤H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p.1≤b → ‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    (∫⁻ ω,ENNReal.ofReal (‖process 𝓕 μ H b I u s ω-process 𝓕 μ H b I u t ω‖^16) ∂μ)≤
      ENNReal.ofReal ((B:ℝ)*(2*K)^8*(b:ℝ)^4*|s-t|^2) := by
  have hh := SingularStoppedMoments.increment 𝓕 μ H I B hBDG u b hK hu
    (HaarUnitTimeMoments.clock b s) (HaarUnitTimeMoments.clock b t)
    (HaarUnitTimeMoments.clock_bound b s) (HaarUnitTimeMoments.clock_bound b t) hbH
  have hd : ((HaarUnitTimeMoments.clock b s:ℝ)-(HaarUnitTimeMoments.clock b t:ℝ))^4≤
      (b:ℝ)^4*|s-t|^2 := by
    rw [HaarUnitTimeMoments.clock_coe b hs,HaarUnitTimeMoments.clock_coe b ht,←mul_sub,mul_pow]
    have hab : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
    have hp := pow_le_pow_of_le_one (abs_nonneg (s-t)) hab (by norm_num : (2:ℕ)≤4)
    have he : |s-t|^4=(s-t)^4 := by rw [←abs_pow,abs_of_nonneg (by positivity)]
    rw [he] at hp
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  exact hh.trans (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring)))

/-- A continuous modification of the original fixed-target stopped
integral, including the singular terminal heat endpoint. -/
def version (t : ℝ≥0) (ω : Ω) : E :=
  KolmogorovModification.modification (process 𝓕 μ H b I u) (HaarContinuousVersion.normalizedTime b t) ω

theorem continuous_version (hb0 : 0<b) (ω : Ω) :
    Continuous (fun t => version 𝓕 μ H b I u t ω) :=
  (KolmogorovModification.continuousOn_modification (process 𝓕 μ H b I u) ω).comp_continuous
    (HaarContinuousVersion.continuous_normalizedTime b) (HaarContinuousVersion.normalizedTime_mem hb0)

theorem version_ae (hbH : b≤H) (hb0 : 0<b) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
    {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p.1≤b → ‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ)))
    (t : ℝ≥0) :
    version 𝓕 μ H b I u t =ᵐ[μ] I.integral (stop 𝓕 μ H (min t b) u) := by
  have he := KolmogorovModification.modification_ae μ (process 𝓕 μ H b I u)
    (fun r _ => process_measurable 𝓕 μ H b I u r) (by positivity : 0≤(B:ℝ)*(2*K)^8*(b:ℝ)^4)
    (fun s hs t ht => increment_moment16 𝓕 μ H b I u hbH B hBDG hK hu hs ht)
    (HaarContinuousVersion.normalizedTime_mem hb0 t)
  change version 𝓕 μ H b I u t=ᵐ[μ]
    I.integral (stop 𝓕 μ H (HaarUnitTimeMoments.clock b (HaarContinuousVersion.normalizedTime b t)) u) at he
  simpa only [HaarContinuousVersion.clock_normalizedTime hb0,NNReal.coe_min] using he

theorem predictable_version (hbH : b≤H) (hb0 : 0<b)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) {K : ℝ} (hK : 0≤K)
    (hu : ∀ᵐ p ∂energyMeasure μ H,p.1≤b → ‖u p‖^2≤K*((b:ℝ)-(p.1:ℝ))^(-(1/2:ℝ))) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (version 𝓕 μ H b I u)) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
  · intro t
    obtain ⟨Z,hZ,he⟩ := I.adapted t (stop 𝓕 μ H (min t b) u) (by
      filter_upwards [stop_stopped 𝓕 μ H (min t b) u] with p hp htp
      exact hp (lt_of_le_of_lt (min_le_left t b) htp))
    exact ⟨Z,hZ,(version_ae 𝓕 μ H b I u hbH hb0 B hBDG hK hu t).trans he⟩
  · exact continuous_version 𝓕 μ H b I u hb0

end SHE.SingularStoppedVersion
