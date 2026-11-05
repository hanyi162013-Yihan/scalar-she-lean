module

public import SHE.RealHeat
public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.PredictableL2
open MeasureTheory Set
open scoped ENNReal NNReal

section Subsigma
variable {X E : Type*} {m m0 : MeasurableSpace X} [NormedAddCommGroup E]
variable (μ : @Measure X m0) (hm : m ≤ m0)

abbrev SubspaceLp := @Lp X E m _ 2 (μ.trim hm)

def ambient (v : SubspaceLp (E := E) μ hm) : @Lp X E m0 _ 2 μ :=
  (memLp_of_memLp_trim hm (Lp.memLp v)).toLp v

theorem ambient_ae (v : SubspaceLp (E := E) μ hm) :
    ambient μ hm v =ᵐ[μ] v := (memLp_of_memLp_trim hm (Lp.memLp v)).coeFn_toLp

theorem ambient_norm (v : SubspaceLp (E := E) μ hm) : ‖ambient μ hm v‖=‖v‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (ambient_ae μ hm v)]
  exact (eLpNorm_trim_ae hm (Lp.aestronglyMeasurable v)).symm

variable [NormedSpace ℝ E]

/-- The actual closed complete-space realization of a coarser measurable
L² process embeds isometrically in its ambient product-measure space. -/
def ambientIsometry : SubspaceLp (E := E) μ hm →ₗᵢ[ℝ] @Lp X E m0 _ 2 μ where
  toFun := ambient μ hm
  map_add' v w := by
    apply Lp.ext
    filter_upwards [ambient_ae μ hm (v+w),ambient_ae μ hm v,ambient_ae μ hm w,
      ae_eq_of_ae_eq_trim (Lp.coeFn_add v w),
      Lp.coeFn_add (ambient μ hm v) (ambient μ hm w)] with x ha hv hw hs ht
    rw [ha,ht]
    simp only [Pi.add_apply,hv,hw,hs]
  map_smul' r v := by
    apply Lp.ext
    filter_upwards [ambient_ae μ hm (r • v),ambient_ae μ hm v,
      ae_eq_of_ae_eq_trim (Lp.coeFn_smul r v),Lp.coeFn_smul r (ambient μ hm v)] with x ha hv hs ht
    simp only [RingHom.id_apply]
    rw [ha,ht]
    simp only [Pi.smul_apply,hv,hs]
  norm_map' := ambient_norm μ hm

omit [NormedSpace ℝ E] in
theorem realization_stronglyMeasurable (v : SubspaceLp (E := E) μ hm) :
    StronglyMeasurable[m0] v := (Lp.stronglyMeasurable v).mono hm

end Subsigma

section Predictable
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)

theorem predictable_le_product : 𝓕.predictable ≤ inferInstanceAs (MeasurableSpace (ℝ≥0 × Ω)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (⊥:ℝ≥0)).prod (𝓕.le _ A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (𝓕.le t A hA)

def timeMeasure (h : ℝ≥0) : Measure ℝ≥0 :=
  ((volume : Measure ℝ).restrict (Ioc 0 (h:ℝ))).comap ((↑) : ℝ≥0 → ℝ)

instance timeMeasure_finite (h : ℝ≥0) : IsFiniteMeasure (timeMeasure h) := by
  unfold timeMeasure
  infer_instance

theorem nonnegative_coe_measurableEmbedding : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Ici

/-- The finite nonnegative-time measure is exactly ordinary Lebesgue
measure on the physical interval after coercion to real time. -/
theorem timeMeasure_map (h : ℝ≥0) :
    (timeMeasure h).map ((↑) : ℝ≥0 → ℝ)=(volume : Measure ℝ).restrict (Ioc 0 (h:ℝ)) := by
  rw [timeMeasure,nonnegative_coe_measurableEmbedding.map_comap]
  have hr : range ((↑) : ℝ≥0 → ℝ)=Ici (0:ℝ) := by
    ext r
    constructor
    · rintro ⟨x,rfl⟩
      exact x.2
    · intro hx
      exact ⟨⟨r,hx⟩,rfl⟩
  rw [hr,Measure.restrict_restrict measurableSet_Ici]
  congr 1
  exact inter_eq_right.mpr (fun _ ht => ht.1.le)

def energyMeasure (μ : Measure Ω) (h : ℝ≥0) : Measure (ℝ≥0 × Ω) :=
  (timeMeasure h).prod μ

/-- Literal square-integrable predictable physical processes. Completeness
comes from the L² space over the trimmed predictable sigma algebra. -/
abbrev Process (μ : Measure Ω) (h : ℝ≥0) :=
  SubspaceLp (E := E) (energyMeasure μ h) (predictable_le_product 𝓕)

def processEmbedding (μ : Measure Ω) (h : ℝ≥0) [NormedSpace ℝ E] :
    Process (E := E) 𝓕 μ h →ₗᵢ[ℝ] Lp E 2 (energyMeasure μ h) :=
  ambientIsometry (energyMeasure μ h) (predictable_le_product 𝓕)

theorem process_isStronglyPredictable (μ : Measure Ω) (h : ℝ≥0)
    (v : Process (E := E) 𝓕 μ h) : IsStronglyPredictable 𝓕 (fun t ω => v (t,ω)) :=
  Lp.stronglyMeasurable v

end Predictable
end SHE.PredictableL2
