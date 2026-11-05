module

public import SHE.PredictableItoRotation
public import SHE.StandardFiniteIto

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RotatedItoAlgebra
open MeasureTheory Set PredictableL2 PredictableItoRotation StoppedItoInputs FiniteItoNoise
open scoped NNReal ENNReal

variable {Ω A C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable (Φ : (ℝ≥0 × Ω) → A →ₗᵢ[ℝ] C)
variable (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p => Φ p.1 p.2))

theorem map_stop (t : ℝ) (v : Process (E := A) 𝓕 μ h) :
    processIsometry 𝓕 μ h Φ hΦ (stop 𝓕 μ h t v)=
      stop 𝓕 μ h t (processIsometry 𝓕 μ h Φ hΦ v) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [processIsometry_ae 𝓕 μ h Φ hΦ (stop 𝓕 μ h t v),stop_ae 𝓕 μ h t v,
    stop_ae 𝓕 μ h t (processIsometry 𝓕 μ h Φ hΦ v),processIsometry_ae 𝓕 μ h Φ hΦ v] with p hm hs ht hv
  rw [hm,hs,ht]
  by_cases hp : p ∈ before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,hv]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,map_zero]

variable {n : ℕ} (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[𝓕.predictable] Y)
variable (R : Fin n → Process (E := A) 𝓕 μ h)

theorem map_gradient (G : ℝ → State n → ℝ) (hG : AdmissibleGradient G) :
    processIsometry 𝓕 μ h Φ hΦ (gradientProcess 𝓕 μ h Y hY R G hG)=
      gradientProcess 𝓕 μ h Y hY (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) G hG := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hall : ∀ᵐ p ∂energyMeasure μ h,∀ i,processIsometry 𝓕 μ h Φ hΦ (R i) p=Φ p (R i p) :=
    ae_all_iff.mpr (fun i => processIsometry_ae 𝓕 μ h Φ hΦ (R i))
  filter_upwards [processIsometry_ae 𝓕 μ h Φ hΦ (gradientProcess 𝓕 μ h Y hY R G hG),
    gradientProcess_ae 𝓕 μ h Y hY R G hG,
    gradientProcess_ae 𝓕 μ h Y hY (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) G hG,hall] with p hm hs ht hr
  rw [hm,hs,ht]
  unfold gradientRow
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,hr i]

theorem noise_rotation (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (a b : ℝ) (G : ℝ → State n → ℝ) :
    noise 𝓕 μ h Y hY R (PredictableItoRotation.integral 𝓕 μ h Φ hΦ J) a b G=
      noise 𝓕 μ h Y hY (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) J a b G := by
  classical
  by_cases hG : AdmissibleGradient G
  · rw [noise_eq 𝓕 μ h Y hY R _ a b G hG,
      noise_eq 𝓕 μ h Y hY (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) J a b G hG]
    change J.integral (processIsometry 𝓕 μ h Φ hΦ
      (stop 𝓕 μ h b (gradientProcess 𝓕 μ h Y hY R G hG)-stop 𝓕 μ h a (gradientProcess 𝓕 μ h Y hY R G hG)))=_
    rw [map_sub,map_stop,map_stop,map_gradient 𝓕 μ h Φ hΦ Y hY R G hG]
  · simp only [noise,dif_neg hG]

theorem vectorIntegral_rotation (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (z : State n) (t : ℝ≥0) :
    StandardFiniteIto.vectorIntegral 𝓕 μ h (PredictableItoRotation.integral 𝓕 μ h Φ hΦ J) z R t=
      StandardFiniteIto.vectorIntegral 𝓕 μ h J z (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) t := by
  funext ω
  apply WithLp.ofLp_injective
  funext i
  change z i+J.integral (processIsometry 𝓕 μ h Φ hΦ (stop 𝓕 μ h t (R i))) ω=
    z i+J.integral (stop 𝓕 μ h t (processIsometry 𝓕 μ h Φ hΦ (R i))) ω
  rw [map_stop]

theorem row_gram_ae : ∀ᵐ p ∂energyMeasure μ h,∀ i j : Fin n,
    inner ℝ (processIsometry 𝓕 μ h Φ hΦ (R i) p) (processIsometry 𝓕 μ h Φ hΦ (R j) p)=
      inner ℝ (R i p) (R j p) := by
  have hall : ∀ᵐ p ∂energyMeasure μ h,∀ i,processIsometry 𝓕 μ h Φ hΦ (R i) p=Φ p (R i p) :=
    ae_all_iff.mpr (fun i => processIsometry_ae 𝓕 μ h Φ hΦ (R i))
  filter_upwards [hall] with p hp i j
  rw [hp i,hp j,(Φ p).inner_map_map]

end SHE.RotatedItoAlgebra
