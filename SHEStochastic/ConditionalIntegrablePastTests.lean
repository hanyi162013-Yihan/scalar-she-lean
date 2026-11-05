module

public import SHEStochastic.ConditionalCountablePastTests
public import SHEStochastic.BCFL1PastTesting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.ConditionalIntegrablePastTests
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω E X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- First moments disintegrate under the actual conditional initial law. -/
theorem integrable (Z : Ω → E) (hZ : Measurable Z) (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ z ∂μ.map Z,Integrable f (condDistrib id Z μ z) :=
  (hf.comp_snd_map_prodMk hZ.aemeasurable).condDistrib_ae_map
    hZ.aemeasurable measurable_id.aemeasurable

/-- Countably many clocks and determining past sets share one
conditional event, using first moments only. -/
theorem identities (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (Z : Ω → E) (hZ₀ : Measurable[F 0] Z) (r : ℕ → ℝ≥0)
    (past : ℝ≥0 → Ω → X) (hpast : ∀ t,Measurable[F t] (past t)) :
    ∀ᵐ z ∂μ.map Z,∀ i j : ℕ,r i≤r j → ∀ A : Set X,MeasurableSet A →
      (∫ sample in past (r i) ⁻¹' A,M (r j) sample-M (r i) sample ∂condDistrib id Z μ z)=0 := by
  have hZ : Measurable Z := hZ₀.mono (F.le 0) le_rfl
  have htest (i j : ℕ) (u : Finset ℕ) : ∀ᵐ z ∂μ.map Z,r i≤r j →
      (∫ sample in past (r i) ⁻¹' CountableIntegralTests.testSet X u,
        M (r j) sample-M (r i) sample ∂condDistrib id Z μ z)=0 := by
    by_cases hst : r i≤r j
    · let A := past (r i) ⁻¹' CountableIntegralTests.testSet X u
      let test : Ω → ℝ := A.indicator (fun _ => 1)
      have hm : MeasurableSet[F (r i)] A := hpast (r i) (CountableIntegralTests.measurable_testSet X u)
      have ha : StronglyMeasurable[F (r i)] test := stronglyMeasurable_const.indicator hm
      have hb (sample : Ω) : ‖test sample‖≤(1 : ℝ≥0) := by
        by_cases hs : sample∈A <;> simp [test,hs]
      have hh := ConditionalMartingaleTests.weighted_increment_integrable μ F M hM Z hZ₀
        (r i) (r j) hst test ha 1 hb
      filter_upwards [hh] with z hz _
      calc
        _ = ∫ sample,test sample*(M (r j) sample-M (r i) sample) ∂condDistrib id Z μ z := by
          rw [←integral_indicator ((F.le (r i)) A hm)]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun sample => by
            by_cases hs : sample∈A <;> simp [test,Set.indicator_apply,hs]
        _ = 0 := hz
    · exact Filter.Eventually.of_forall fun _ h => (hst h).elim
  have hall := ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr (htest i j)
  have hmem := ae_all_iff.mpr fun i => integrable μ Z hZ (M (r i)) (hM.integrable (r i))
  filter_upwards [hall,hmem] with z hz hm i j hst A hA
  exact CountableIntegralTests.extend X (condDistrib id Z μ z) (past (r i))
    ((hpast (r i)).mono (F.le (r i)) le_rfl) (fun sample => M (r j) sample-M (r i) sample)
    ((hm j).sub (hm i)) (fun u => hz i j u hst) A hA

/-- A continuous martingale with an integrable path envelope survives
initial-state disintegration in the full canonical past. Its compensator
need not have a second moment. -/
theorem martingale [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M F μ) (hc : ∀ sample,Continuous (fun t => M t sample))
    (D : Ω → ℝ) (hD : Integrable D μ) (hb : ∀ t sample,‖M t sample‖≤D sample)
    (Z : Ω → E) (hZ₀ : Measurable[F 0] Z)
    (past : ℝ≥0 → Ω → X) (hpast : ∀ t,Measurable[F t] (past t))
    (hpc : ∀ sample,Continuous (fun t => past t sample))
    (hF : ∀ t,F t≤MeasurableSpace.comap (past t) inferInstance) :
    ∀ᵐ z ∂μ.map Z,Martingale M F (condDistrib id Z μ z) := by
  obtain ⟨r,hr⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hZ : Measurable Z := hZ₀.mono (F.le 0) le_rfl
  filter_upwards [identities μ F M hM Z hZ₀ r past hpast,integrable μ Z hZ D hD] with z hz hd
  have hm (t : ℝ≥0) : Integrable (M t) (condDistrib id Z μ z) :=
    hd.mono' ((hM.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hb t))
  apply BCFL1PastTesting.martingale (condDistrib id Z μ z) F past
    (fun t => (hpast t).mono (F.le t) le_rfl) hF M hM.stronglyAdapted hm
  intro s t hst ψ
  apply DenseClockIntegralTests.zero_of_dense (condDistrib id Z μ z) M
    (fun t => ((hM.stronglyAdapted t).mono (F.le t)).measurable) hc past
    (fun t => (hpast t).mono (F.le t) le_rfl) hpc D hd hb r hr ?_ s t hst ψ
  intro i j hij ψ
  exact ConditionalCountablePastTests.weighted_of_sets (condDistrib id Z μ z) (past (r i))
    ((hpast (r i)).mono (F.le (r i)) le_rfl) (fun sample => M (r j) sample-M (r i) sample)
    ((hm _).sub (hm _)) (hz i j hij) ψ

end SHEStochastic.ConditionalIntegrablePastTests
