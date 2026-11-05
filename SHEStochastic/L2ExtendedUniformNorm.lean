module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.L2ExtendedUniformNorm
open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  (ν : Measure X) [IsFiniteMeasure ν]

/-- The extended essential uniform norm is defined on actual L² classes,
including classes with no bounded or continuous representative. -/
def value (u : Lp E 2 ν) : ℝ≥0∞ := eLpNorm (u : X → E) ∞ ν

theorem le_iff (u : Lp E 2 ν) (a : ℝ≥0∞) :
    value ν u ≤ a ↔ ∀ᵐ x ∂ν, ‖u x‖ₑ ≤ a := by
  rw [value, eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
  constructor
  · intro h
    exact (ae_le_eLpNormEssSup (f := (u : X → E))).mono fun _ hx ↦ hx.trans h
  · exact eLpNormEssSup_le_of_ae_enorm_bound

theorem le_ofReal_iff (u : Lp E 2 ν) (M : ℝ) (hM : 0 ≤ M) :
    value ν u ≤ ENNReal.ofReal M ↔ ∀ᵐ x ∂ν, ‖u x‖ ≤ M := by
  rw [le_iff]
  constructor
  · intro h
    filter_upwards [h] with x hx
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
    change (‖u x‖ₑ).toReal ≤ (ENNReal.ofReal M).toReal at hh
    simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
      ENNReal.toReal_ofReal hM] using hh
  · intro h
    filter_upwards [h] with x hx
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx

theorem add_le (u v : Lp E 2 ν) : value ν (u + v) ≤ value ν u + value ν v := by
  calc
    _ = eLpNorm ((u : X → E) + (v : X → E)) ∞ ν := eLpNorm_congr_ae (Lp.coeFn_add u v)
    _ ≤ _ := eLpNorm_add_le le_top

/-- Uniform-norm sublevels are closed in the L² topology. The proof
reuses the almost-everywhere subsequence of an L²-convergent sequence. -/
theorem isClosed_sublevel (a : ℝ≥0∞) : IsClosed {u : Lp E 2 ν | value ν u ≤ a} := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv
  obtain ⟨ns, _, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  apply (le_iff ν v a).mpr
  have hbound : ∀ᵐ x ∂ν, ∀ n, ‖u (ns n) x‖ₑ ≤ a :=
    ae_all_iff.mpr (fun n ↦ (le_iff ν _ a).mp (hu (ns n)))
  filter_upwards [hbound, hlim] with x hx ht
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht.norm
  have hn : ∀ n, ENNReal.ofReal ‖u (ns n) x‖ ≤ a := by
    intro n
    simpa only [ofReal_norm] using hx n
  simpa only [ofReal_norm] using le_of_tendsto' hh hn

theorem lowerSemicontinuous : LowerSemicontinuous (value (E := E) ν) :=
  lowerSemicontinuous_iff_isClosed_preimage.mpr (isClosed_sublevel ν)

/-- L2 continuity supplies the lower semicontinuous half. A continuous
upper envelope touching the uniform norm at the initial state supplies
the other half, without L-infinity continuity of the initial heat orbit. -/
theorem continuousAt_of_envelope {A : Type*} [TopologicalSpace A]
    (U : A → Lp E 2 ν) (x : A) (hU : ContinuousAt U x)
    (B : A → ℝ≥0∞) (hB : ContinuousAt B x)
    (hbound : ∀ᶠ t in 𝓝 x, value ν (U t) ≤ B t) (heq : value ν (U x) = B x) :
    ContinuousAt (fun t ↦ value ν (U t)) x := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨(lowerSemicontinuous ν (U x)).comp hU, ?_⟩
  intro b hb
  change value ν (U x) < b at hb
  rw [heq] at hb
  filter_upwards [hbound, hB.upperSemicontinuousAt b hb] with t ht hbt
  exact ht.trans_lt hbt

local instance : MeasurableSpace (Lp E 2 ν) := borel _
local instance : BorelSpace (Lp E 2 ν) := ⟨rfl⟩

/-- In particular the extended uniform norm is a Borel path-state
functional, as required when defining closed-level exit times in L². -/
theorem measurable : Measurable (value (E := E) ν) := by
  apply measurable_of_Iic
  intro a
  exact (isClosed_sublevel ν a).measurableSet

/-- The real state observable used in Borel path reconstruction. On
the bounded states occurring along a regular solution it equals the
usual uniform norm. The value at infinity is immaterial to that support. -/
def realValue (u : Lp E 2 ν) : ℝ := (value ν u).toReal

theorem measurable_realValue : Measurable (realValue (E := E) ν) :=
  ENNReal.measurable_toReal.comp (measurable ν)

theorem realValue_nonneg (u : Lp E 2 ν) : 0 ≤ realValue ν u := ENNReal.toReal_nonneg

/-- For a continuous representative the extended essential norm is
exactly its uniform norm. This connects positive-time spatial continuity
to the Borel state functional used by the exit time. -/
theorem continuous_representative [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    [NormedSpace ℝ E] [SecondCountableTopology E] [ν.IsOpenPosMeasure]
    (f : C(X, E)) :
    value ν ((ContinuousMap.toLp 2 ν ℝ) f) = ENNReal.ofReal ‖f‖ := by
  let u := (ContinuousMap.toLp 2 ν ℝ) f
  have hrep : u =ᵐ[ν] f := ContinuousMap.coeFn_toLp ν f
  apply le_antisymm
  · apply (le_iff ν u _).mpr
    filter_upwards [hrep] with x hx
    rw [hx, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (f.norm_coe_le_norm x)
  · change ENNReal.ofReal ‖f‖ ≤ value ν u
    by_cases ha : value ν u = ∞
    · simp only [ha, le_top]
    · have hbound : ∀ᵐ x ∂ν, ‖f x‖ ≤ (value ν u).toReal := by
        filter_upwards [(le_iff ν u (value ν u)).mp le_rfl, hrep] with x hx he
        rw [he, ← ofReal_norm] at hx
        have hh := ENNReal.toReal_mono ha hx
        simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hh
      have hclosed : IsClosed {x | ‖f x‖ ≤ (value ν u).toReal} :=
        isClosed_le f.continuous.norm continuous_const
      have hall : {x | ‖f x‖ ≤ (value ν u).toReal} = univ :=
        hclosed.ae_eq_univ_iff_eq.mp (ae_eq_univ.mpr hbound)
      have hn : ‖f‖ ≤ (value ν u).toReal := (f.norm_le ENNReal.toReal_nonneg).mpr fun x ↦ by
        change x ∈ {x | ‖f x‖ ≤ (value ν u).toReal}
        rw [hall]
        trivial
      calc
        _ ≤ ENNReal.ofReal (value ν u).toReal := ENNReal.ofReal_le_ofReal hn
        _ = _ := ENNReal.ofReal_toReal ha

end SHEStochastic.L2ExtendedUniformNorm
