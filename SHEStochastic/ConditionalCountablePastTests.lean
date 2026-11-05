module

public import SHEStochastic.ConditionalMartingaleTests
public import SHEStochastic.CountableIntegralTests
public import SHEStochastic.DenseClockIntegralTests
public import SHEStochastic.DoobL2Envelope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.ConditionalCountablePastTests
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω E X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem memLp_two (Z : Ω → E) (hZ : Measurable Z) (f : Ω → ℝ) (hm : StronglyMeasurable f)
    (hf : MemLp f 2 μ) : ∀ᵐ z ∂μ.map Z, MemLp f 2 (condDistrib id Z μ z) := by
  have hi := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hf
  have hh := (hi.comp_snd_map_prodMk hZ.aemeasurable).condDistrib_ae_map
    hZ.aemeasurable measurable_id.aemeasurable
  filter_upwards [hh] with z hz
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hz

/-- One conditional initial-state event supports every measurable past
test at every pair from a prescribed countable collection of clocks. -/
theorem identities (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (Z : Ω → E) (hZ₀ : Measurable[F 0] Z) (r : ℕ → ℝ≥0)
    (past : ℝ≥0 → Ω → X) (hpast : ∀ t, Measurable[F t] (past t)) :
    ∀ᵐ z ∂μ.map Z, ∀ i j : ℕ, r i ≤ r j → ∀ A : Set X, MeasurableSet A →
      (∫ sample in past (r i) ⁻¹' A, M (r j) sample-M (r i) sample ∂condDistrib id Z μ z) = 0 := by
  have hZ : Measurable Z := hZ₀.mono (F.le 0) le_rfl
  have htest (i j : ℕ) (u : Finset ℕ) : ∀ᵐ z ∂μ.map Z, r i ≤ r j →
      (∫ sample in past (r i) ⁻¹' CountableIntegralTests.testSet X u,
        M (r j) sample-M (r i) sample ∂condDistrib id Z μ z) = 0 := by
    by_cases hst : r i ≤ r j
    · let A := past (r i) ⁻¹' CountableIntegralTests.testSet X u
      let test : Ω → ℝ := A.indicator (fun _ ↦ 1)
      have hm : MeasurableSet[F (r i)] A := hpast (r i) (CountableIntegralTests.measurable_testSet X u)
      have ha : StronglyMeasurable[F (r i)] test := stronglyMeasurable_const.indicator hm
      have hb (sample : Ω) : ‖test sample‖ ≤ (1 : ℝ≥0) := by
        by_cases hs : sample ∈ A <;> simp [test, hs]
      have hh := ConditionalMartingaleTests.weighted_increment μ F M hM hM2 Z hZ₀
        (r i) (r j) hst test ha 1 hb
      filter_upwards [hh] with z hz _
      calc
        _ = ∫ sample, test sample*(M (r j) sample-M (r i) sample) ∂condDistrib id Z μ z := by
          rw [← integral_indicator ((F.le (r i)) A hm)]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun sample ↦ by
            by_cases hs : sample ∈ A <;> simp [test, Set.indicator_apply, hs]
        _ = 0 := hz
    · exact Filter.Eventually.of_forall fun _ h ↦ (hst h).elim
  have hall := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ ae_all_iff.mpr (htest i j)
  have hmem := ae_all_iff.mpr fun i ↦ memLp_two μ Z hZ (M (r i))
    ((hM.stronglyAdapted (r i)).mono (F.le (r i))) (hM2 (r i))
  filter_upwards [hall, hmem] with z hz hm i j hst A hA
  exact CountableIntegralTests.extend X (condDistrib id Z μ z) (past (r i))
    ((hpast (r i)).mono (F.le (r i)) le_rfl) (fun sample ↦ M (r j) sample-M (r i) sample)
    (((hm j).integrable one_le_two).sub ((hm i).integrable one_le_two))
    (fun u ↦ hz i j u hst) A hA

theorem weighted_of_sets {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (past : Ω → Y) (hpast : Measurable past) (f : Ω → ℝ) (hf : Integrable f μ)
    (hzero : ∀ A : Set Y, MeasurableSet A → (∫ sample in past ⁻¹' A, f sample ∂μ) = 0)
    (ψ : BoundedContinuousFunction Y ℝ) : (∫ sample, ψ (past sample)*f sample ∂μ) = 0 := by
  let m := MeasurableSpace.comap past inferInstance
  have hpc : @Measurable Ω Y m inferInstance past := Measurable.of_comap_le le_rfl
  have hψ : StronglyMeasurable[m] (fun sample ↦ ψ (past sample)) :=
    (ψ.continuous.measurable.comp hpc).stronglyMeasurable
  have hi := hf.bdd_mul (ψ.continuous.measurable.comp hpast).stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun sample ↦ ψ.norm_coe_le_norm (past sample))
  have hc : μ[f | m] =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq hpast.comap_le hf
      (fun _ _ _ ↦ (integrable_const (0 : ℝ)).integrableOn) (fun A hA _ ↦ ?_)
      stronglyMeasurable_zero.aestronglyMeasurable).symm
    rcases hA with ⟨B, hB, rfl⟩
    rw [integral_zero]
    exact (hzero B hB).symm
  have hh := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ) hψ hi hf
  change μ[fun sample ↦ ψ (past sample)*f sample | m] =ᵐ[μ]
    fun sample ↦ ψ (past sample)*μ[f | m] sample at hh
  calc
    _ = ∫ sample, μ[fun sample ↦ ψ (past sample)*f sample | m] sample ∂μ :=
      (integral_condExp hpast.comap_le).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hh, hc] with sample hh hc
      change μ[fun sample ↦ ψ (past sample)*f sample | m] sample = 0
      rw [hh, hc, mul_zero]

theorem measurable_envelope (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (hc : ∀ sample, Continuous (fun t ↦ M t sample)) (H : ℝ≥0) (hT : MemLp (M H) 2 μ)
    (hclip : ∀ t, M t = M (min t H)) :
    ∃ D : Ω → ℝ, Measurable D ∧ MemLp D 2 μ ∧ (∀ sample, 0 ≤ D sample) ∧
      ∀ t sample, ‖M t sample‖ ≤ D sample := by
  obtain ⟨D, hD, hD0, hb, ha⟩ := DoobL2Envelope.exists_envelope hM hc H hT
  have hcompact : IsCompact (Set.Iic H : Set ℝ≥0) := by
    convert isCompact_Icc (a := (0 : ℝ≥0)) (b := H) using 1
    ext t
    simp
  letI : CompactSpace (Set.Iic H) := isCompact_iff_compactSpace.mp hcompact
  let path (sample : Ω) : C(Set.Iic H, ℝ) := ⟨fun t ↦ M t sample, (hc sample).comp continuous_subtype_val⟩
  have hm : Measurable path := ContinuousMap.measurable_iff_eval.mpr fun t ↦
    ((hM.stronglyAdapted t).mono (F.le t)).measurable
  have he : D = fun sample ↦ ‖path sample‖ := by
    funext sample
    apply le_antisymm
    · obtain ⟨t, ht, hat⟩ := ha sample
      rw [hat]
      exact (path sample).norm_coe_le_norm ⟨t, ht⟩
    · exact ((path sample).norm_le (hD0 sample)).mpr fun t ↦ hb t t.property sample
  refine ⟨D, by rw [he]; exact hm.norm, hD, hD0, ?_⟩
  intro t sample
  rw [hclip t]
  exact hb (min t H) (min_le_right _ _) sample

/-- Disintegration at a known initial state preserves a continuous L2
martingale on the FULL history filtration, at every clock. Doob supplies
the domination needed for the dense-time closure; it is not a new input. -/
theorem martingale [MetricSpace X] [BorelSpace X]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ sample, Continuous (fun t ↦ M t sample))
    (H : ℝ≥0) (hclip : ∀ t, M t = M (min t H))
    (Z : Ω → E) (hZ₀ : Measurable[F 0] Z)
    (past : ℝ≥0 → Ω → X) (hpast : ∀ t, Measurable[F t] (past t))
    (hpc : ∀ sample, Continuous (fun t ↦ past t sample))
    (hF : ∀ t, F t ≤ MeasurableSpace.comap (past t) inferInstance) :
    ∀ᵐ z ∂μ.map Z, Martingale M F (condDistrib id Z μ z) ∧
      ∀ t, MemLp (M t) 2 (condDistrib id Z μ z) := by
  obtain ⟨r, hr⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  obtain ⟨D, hDm, hD, hD0, hb⟩ := measurable_envelope μ F M hM hc H (hM2 H) hclip
  have hZ : Measurable Z := hZ₀.mono (F.le 0) le_rfl
  have hd := memLp_two μ Z hZ D hDm.stronglyMeasurable hD
  filter_upwards [identities μ F M hM hM2 Z hZ₀ r past hpast, hd] with z hz hd
  have hm2 (t : ℝ≥0) : MemLp (M t) 2 (condDistrib id Z μ z) := by
    apply hd.mono ((hM.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun sample ↦ (hb t sample).trans (le_abs_self _)
  refine ⟨?_, hm2⟩
  apply BCFPastTesting.martingale (condDistrib id Z μ z) F past
    (fun t ↦ (hpast t).mono (F.le t) le_rfl) hF M hM.stronglyAdapted hm2
  intro s t hst ψ
  apply DenseClockIntegralTests.zero_of_dense (condDistrib id Z μ z) M
    (fun t ↦ ((hM.stronglyAdapted t).mono (F.le t)).measurable) hc past
    (fun t ↦ (hpast t).mono (F.le t) le_rfl) hpc D (hd.integrable one_le_two) hb r hr ?_ s t hst ψ
  intro i j hij ψ
  exact weighted_of_sets (condDistrib id Z μ z) (past (r i))
    ((hpast (r i)).mono (F.le (r i)) le_rfl) (fun sample ↦ M (r j) sample-M (r i) sample)
    (((hm2 _).integrable one_le_two).sub ((hm2 _).integrable one_le_two)) (hz i j hij) ψ

end SHEStochastic.ConditionalCountablePastTests
