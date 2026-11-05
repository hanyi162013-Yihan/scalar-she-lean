module

public import SHE.TimeDilationIto
public import SHE.StandardFiniteIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.ClockedItoAlgebra
open MeasureTheory Set Filter PredictableL2 PredictableTimeDilation StoppedItoInputs FiniteItoNoise
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

theorem ae_clock {P : (ℝ≥0×Ω)→Prop}
    (hP : ∀ᵐ p ∂energyMeasure μ (c*h),P p) :
    ∀ᵐ p ∂energyMeasure μ h,P (clock c hc p.1,p.2) :=
  ScaledLpPull.ae_comp (energyMeasure μ h) (energyMeasure μ (c*h)) (c:ℝ) hc
    (fun p => (clock c hc p.1,p.2)) (energyMeasure_clock_preserving c hc h μ) hP

theorem map_stop (t : ℝ) (v : Process (E := C) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    processIsometry 𝓕 μ c hc h (stop (filtration 𝓕 (clock c hc)) μ (c*h) t v)=
      stop 𝓕 μ h (t/(c:ℝ)) (processIsometry 𝓕 μ c hc h v) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hstop := ae_clock μ c hc h (stop_ae (filtration 𝓕 (clock c hc)) μ (c*h) t v)
  filter_upwards [processIsometry_ae 𝓕 μ c hc h (stop (filtration 𝓕 (clock c hc)) μ (c*h) t v),
    hstop,stop_ae 𝓕 μ h (t/(c:ℝ)) (processIsometry 𝓕 μ c hc h v),processIsometry_ae 𝓕 μ c hc h v]
    with p hm hs ht hv
  rw [hm,hs,ht]
  have hmem : (clock c hc p.1,p.2)∈before (Ω := Ω) t↔p∈before (Ω := Ω) (t/(c:ℝ)) := by
    change (c:ℝ)*(p.1:ℝ)<t↔(p.1:ℝ)<t/(c:ℝ)
    rw [lt_div_iff₀ (show 0<(c:ℝ) from hc),mul_comm (p.1:ℝ)]
  by_cases hp : p∈before (Ω := Ω) (t/(c:ℝ))
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (hmem.mpr hp),hv]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem (mt hmem.mp hp),smul_zero]

def state {n : ℕ} (Y : ℝ≥0×Ω→State n) (p : ℝ≥0×Ω) : State n := Y (clock c hc p.1,p.2)

theorem state_predictable {n : ℕ} (Y : ℝ≥0×Ω→State n)
    (hY : StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] Y) :
    StronglyMeasurable[𝓕.predictable] (state c hc Y) :=
  hY.comp_measurable (measurable_forward 𝓕 (clock c hc))

def test {n : ℕ} (G : ℝ→State n→ℝ) (t : ℝ) : State n→ℝ := G ((c:ℝ)*t)

theorem admissible {n : ℕ} {G : ℝ→State n→ℝ} (hG : AdmissibleGradient G) :
    AdmissibleGradient (test c G) := by
  constructor
  · exact hG.1.comp (((continuous_const (y := (c:ℝ))).mul continuous_fst).prodMk continuous_snd)
  · obtain ⟨L,hL⟩ := hG.2
    exact ⟨L,fun t z => hL ((c:ℝ)*t) z⟩

variable {n : ℕ} (Y : ℝ≥0×Ω→State n)
variable (hY : StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] Y)
variable (R : Fin n→Process (E := C) (filtration 𝓕 (clock c hc)) μ (c*h))

theorem map_gradient (G : ℝ→State n→ℝ) (hG : AdmissibleGradient G) :
    processIsometry 𝓕 μ c hc h
      (gradientProcess (filtration 𝓕 (clock c hc)) μ (c*h) Y hY R G hG)=
    gradientProcess 𝓕 μ h (state c hc Y) (state_predictable 𝓕 c hc Y hY)
      (fun i => processIsometry 𝓕 μ c hc h (R i)) (test c G) (admissible c hG) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hgrad := ae_clock μ c hc h (gradientProcess_ae (filtration 𝓕 (clock c hc)) μ (c*h) Y hY R G hG)
  have hall : ∀ᵐ p ∂energyMeasure μ h,∀ i,processIsometry 𝓕 μ c hc h (R i) p=
      Real.sqrt (c:ℝ) • R i (clock c hc p.1,p.2) :=
    ae_all_iff.mpr (fun i => processIsometry_ae 𝓕 μ c hc h (R i))
  filter_upwards [processIsometry_ae 𝓕 μ c hc h
      (gradientProcess (filtration 𝓕 (clock c hc)) μ (c*h) Y hY R G hG),hgrad,
    gradientProcess_ae 𝓕 μ h (state c hc Y) (state_predictable 𝓕 c hc Y hY)
      (fun i => processIsometry 𝓕 μ c hc h (R i)) (test c G) (admissible c hG),hall]
    with p hm hs ht hr
  rw [hm,hs,ht]
  unfold gradientRow
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i,smul_smul,smul_smul]
  have hg : gradientCoefficient Y G i (clock c hc p.1,p.2)=
      gradientCoefficient (state c hc Y) (test c G) i p := rfl
  rw [hg,mul_comm]

theorem noise_clock (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (a b : ℝ) (G : ℝ→State n→ℝ) (hG : AdmissibleGradient G) :
    noise (filtration 𝓕 (clock c hc)) μ (c*h) Y hY R (integral 𝓕 μ c hc h J) a b G=
      noise 𝓕 μ h (state c hc Y) (state_predictable 𝓕 c hc Y hY)
        (fun i => processIsometry 𝓕 μ c hc h (R i)) J (a/(c:ℝ)) (b/(c:ℝ)) (test c G) := by
  rw [noise_eq _ _ _ _ _ _ _ _ _ _ hG,
    noise_eq _ _ _ _ _ _ _ _ _ _ (admissible c hG)]
  change J.integral (processIsometry 𝓕 μ c hc h (_-_))=_
  rw [map_sub,map_stop,map_stop,map_gradient 𝓕 μ c hc h Y hY R G hG]

theorem vectorIntegral_clock (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (z : State n) (s : ℝ≥0) :
    StandardFiniteIto.vectorIntegral (filtration 𝓕 (clock c hc)) μ (c*h) (integral 𝓕 μ c hc h J)
      z R (clock c hc s)=
    StandardFiniteIto.vectorIntegral 𝓕 μ h J z (fun i => processIsometry 𝓕 μ c hc h (R i)) s := by
  funext ω
  apply WithLp.ofLp_injective
  funext i
  change z i+J.integral (processIsometry 𝓕 μ c hc h
    (stop (filtration 𝓕 (clock c hc)) μ (c*h) (clock c hc s) (R i))) ω=
      z i+J.integral (stop 𝓕 μ h s (processIsometry 𝓕 μ c hc h (R i))) ω
  rw [map_stop]
  have htime : ((clock c hc s:ℝ≥0):ℝ)/(c:ℝ)=(s:ℝ) := by
    change (c:ℝ)*(s:ℝ)/(c:ℝ)=(s:ℝ)
    exact mul_div_cancel_left₀ _ (show (c:ℝ)≠0 from (show 0<(c:ℝ) from hc).ne')
  rw [htime]

end SHE.ClockedItoAlgebra
