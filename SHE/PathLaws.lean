module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import SHE.Laws

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory

section CompactTime
variable {Time E : Type*}
variable [MetricSpace Time] [CompactSpace Time] [SecondCountableTopology Time]
variable [MeasurableSpace Time] [BorelSpace Time]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [SecondCountableTopology E]
variable (μ : Measure Time) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
variable [MeasurableSpace C(Time, E)] [BorelSpace C(Time, E)]
variable [MeasurableSpace (Lp E 2 μ)] [BorelSpace (Lp E 2 μ)]

/-- The continuous-path inclusion in integrated L2 is a Borel embedding.
The time measure has full support, so continuous paths equal almost everywhere
are equal at every time. Polishness supplies the Borel inverse on the image. -/
theorem integratedPath_measurableEmbedding :
    MeasurableEmbedding (ContinuousMap.toLp (E := E) 2 μ ℝ) := by
  exact (ContinuousMap.toLp (E := E) 2 μ ℝ).continuous.measurableEmbedding
    (ContinuousMap.toLp_injective μ)

/-- Equality of integrated path laws determines the full continuous-path law. -/
theorem continuous_path_laws_eq_of_integrated_laws
    (P Q : ProbabilityMeasure C(Time, E))
    (h : P.map (ContinuousMap.toLp (E := E) 2 μ ℝ) =
      Q.map (ContinuousMap.toLp (E := E) 2 μ ℝ)) : P = Q := by
  apply Subtype.ext
  apply (integratedPath_measurableEmbedding (E := E) μ).map_injective
  exact congrArg (fun ν : ProbabilityMeasure (Lp E 2 μ) => (ν : Measure (Lp E 2 μ))) h

/-- The canonical comparison argument may be performed in integrated L2;
this theorem returns equality on the original continuous-path space. -/
theorem continuous_path_laws_eq_of_integrated_comparisons
    (P Q : ProbabilityMeasure C(Time, E)) (ν : ℕ → ProbabilityMeasure (Lp E 2 μ))
    (eP eQ : ℕ → ℝ)
    (heP : Filter.Tendsto eP Filter.atTop (nhds 0))
    (heQ : Filter.Tendsto eQ Filter.atTop (nhds 0))
    (h : ∀ (f : Lp E 2 μ → ℝ),
      (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) → (∃ L, LipschitzWith L f) →
      ∃ A : ℝ, ∀ n,
        |(∫ x, f x ∂(P.map (ContinuousMap.toLp (E := E) 2 μ ℝ))) -
          (∫ x, f x ∂(ν n))| ≤ A * eP n ∧
        |(∫ x, f x ∂(Q.map (ContinuousMap.toLp (E := E) 2 μ ℝ))) -
          (∫ x, f x ∂(ν n))| ≤ A * eQ n) : P = Q := by
  apply continuous_path_laws_eq_of_integrated_laws μ P Q
  exact laws_eq_of_scaled_common_comparisons _ _ ν eP eQ heP heQ h

end CompactTime
end SHE

namespace SHE
open MeasureTheory Set

/-- A full-support measure remains full-support on a regular closed subtype.
This includes a nondegenerate closed time interval with Lebesgue measure. -/
theorem openPos_comap_subtype_regularClosed
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] {s : Set X}
    (hs : MeasurableSet s) (hregular : closure (interior s) = s) :
    (μ.comap (Subtype.val : s → X)).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hemb := MeasurableEmbedding.subtype_coe hs
  rw [hemb.comap_apply]
  have himage : (Subtype.val : s → X) '' U = V ∩ s := by
    rw [← hVU]
    ext x
    simp only [mem_image, mem_preimage, mem_inter_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hxV, hxs⟩
      exact ⟨⟨x,hxs⟩, hxV, rfl⟩
  rw [himage]
  have hnon : (closure (interior s) ∩ V).Nonempty := by
    rw [hregular]
    obtain ⟨u,hu⟩ := hUne
    refine ⟨u.val, u.property, ?_⟩
    rw [← hVU] at hu
    exact hu
  have hnon' : (interior s ∩ V).Nonempty :=
    (closure_inter_open_nonempty_iff hV).mp hnon
  have hpos : 0 < μ (interior s ∩ V) := (isOpen_interior.inter hV).measure_pos μ hnon'
  apply ne_of_gt
  exact hpos.trans_le (measure_mono (by intro x hx; exact ⟨hx.2, interior_subset hx.1⟩))

end SHE

namespace SHE
open MeasureTheory Set

/-- Lebesgue time measure on the compact interval [0,T], without endpoint atoms. -/
def timeMeasure (T : ℝ) : Measure (Icc (0 : ℝ) T) :=
  volume.comap (Subtype.val : Icc (0 : ℝ) T → ℝ)

theorem timeMeasure_univ (T : ℝ) : timeMeasure T Set.univ = ENNReal.ofReal T := by
  rw [timeMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  have hi : (Subtype.val : Icc (0 : ℝ) T → ℝ) '' Set.univ = Icc (0 : ℝ) T := by ext x; simp
  rw [hi, Real.volume_Icc, sub_zero]

instance timeMeasure_finite (T : ℝ) : IsFiniteMeasure (timeMeasure T) :=
  ⟨by rw [timeMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem timeMeasure_openPos {T : ℝ} (hT : 0 < T) : (timeMeasure T).IsOpenPosMeasure := by
  exact openPos_comap_subtype_regularClosed volume measurableSet_Icc
    (closure_interior_Icc (ne_of_lt hT))

section TimeInterval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [SecondCountableTopology E]
variable {T : ℝ}
variable [MeasurableSpace C(Icc (0 : ℝ) T, E)] [BorelSpace C(Icc (0 : ℝ) T, E)]
variable [MeasurableSpace (Lp E 2 (timeMeasure T))] [BorelSpace (Lp E 2 (timeMeasure T))]

/-- The manuscript's continuous-to-integrated path-law implication for
actual Lebesgue time measure and any complete separable real normed state space. -/
theorem interval_path_laws_eq_of_integrated_laws (hT : 0 < T)
    (P Q : ProbabilityMeasure C(Icc (0 : ℝ) T, E))
    (h : P.map (ContinuousMap.toLp (E := E) 2 (timeMeasure T) ℝ) =
      Q.map (ContinuousMap.toLp (E := E) 2 (timeMeasure T) ℝ)) : P = Q := by
  have := timeMeasure_openPos hT
  exact continuous_path_laws_eq_of_integrated_laws (timeMeasure T) P Q h

end TimeInterval
end SHE
