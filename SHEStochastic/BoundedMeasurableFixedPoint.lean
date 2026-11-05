module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.BoundedMeasurableFixedPoint
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

abbrev BoundedFunctions := lp (fun _ : X => E) ∞

def functionSet (S : Set E) : Set (BoundedFunctions (X := X) (E := E)) :=
  {f | Measurable (f : X → E) ∧ ∀ p, f p ∈ S}

theorem functionSet_closed {S : Set E} (hS : IsClosed S) :
    IsClosed (functionSet (X := X) S) := by
  apply IsSeqClosed.isClosed
  intro u f hu hlim
  have hp : ∀ p, Tendsto (fun n => u n p) atTop (𝓝 (f p)) := fun p =>
    ((lp.evalCLM ℝ (fun _ : X => E) ∞ p).continuous.tendsto f).comp hlim
  refine ⟨measurable_of_tendsto_metrizable (fun n => (hu n).1) (tendsto_pi_nhds.mpr hp), ?_⟩
  exact fun p => hS.mem_of_tendsto (hp p) (Eventually.of_forall fun n => (hu n).2 p)

abbrev Space (S : Set E) := {f : BoundedFunctions (X := X) (E := E) // f ∈ functionSet S}

/-- A reusable complete-function-space realization for bounded measurable
updates with values in an arbitrary closed bounded constraint set. -/
theorem exists_fixedPoint {S : Set E} (hS : IsClosed S) (b : E) (hb : b ∈ S)
    (M : ℝ) (hM : ∀ z ∈ S, ‖z‖ ≤ M)
    (F : (X → E) → X → E)
    (hFm : ∀ f, Measurable f → (∀ p, f p ∈ S) → Measurable (F f))
    (hFS : ∀ f, Measurable f → (∀ p, f p ∈ S) → ∀ p, F f p ∈ S)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hLip : ∀ f g, Measurable f → Measurable g → (∀ p, f p ∈ S) → (∀ p, g p ∈ S) →
      ∀ D : ℝ, 0 ≤ D → (∀ p, ‖f p-g p‖ ≤ D) → ∀ p, ‖F f p-F g p‖ ≤ q*D) :
    ∃ f : X → E, Measurable f ∧ (∀ p, f p ∈ S) ∧ F f = f := by
  classical
  letI : CompleteSpace (Space (X := X) S) := (functionSet_closed hS).completeSpace_coe
  let bfun : BoundedFunctions (X := X) (E := E) :=
    ⟨fun _ => b, memℓp_infty ⟨‖b‖, by rintro _ ⟨p, rfl⟩; exact le_rfl⟩⟩
  letI : Nonempty (Space (X := X) S) := ⟨⟨bfun, measurable_const, fun _ => hb⟩⟩
  let T : Space (X := X) S → Space (X := X) S := fun f =>
    ⟨⟨F f.val, memℓp_infty ⟨M, by
      rintro _ ⟨p, rfl⟩
      exact hM _ (hFS _ f.property.1 f.property.2 p)⟩⟩,
      hFm _ f.property.1 f.property.2, hFS _ f.property.1 f.property.2⟩
  let K : ℝ≥0 := ⟨q,hq⟩
  have hT : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖(T f).val-(T g).val‖ ≤ q*‖f.val-g.val‖
    apply lp.norm_le_of_forall_le (mul_nonneg hq (norm_nonneg _))
    apply hLip f.val g.val f.property.1 g.property.1 f.property.2 g.property.2 _ (norm_nonneg _)
    intro p
    change ‖(f.val-g.val) p‖ ≤ ‖f.val-g.val‖
    exact lp.norm_apply_le_norm (by norm_num : (∞ : ℝ≥0∞) ≠ 0) _ p
  have hc : ContractingWith K T := ⟨hq1,hT⟩
  let f := hc.fixedPoint T
  refine ⟨f.val,f.property.1,f.property.2,?_⟩
  funext p
  exact congrArg (fun g : Space (X := X) S => g.val p) hc.fixedPoint_isFixedPt

/-- Pointwise bounded functions agreeing with a uniform strict contraction
agree everywhere; this also applies when no measurability is required. -/
theorem eq_of_contraction (f g : X → E) (M q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ p, ‖f p‖ ≤ M) (hg : ∀ p, ‖g p‖ ≤ M)
    (hstep : ∀ D : ℝ, 0 ≤ D → (∀ p, ‖f p-g p‖ ≤ D) → ∀ p, ‖f p-g p‖ ≤ q*D) : f = g := by
  let flp : BoundedFunctions (X := X) (E := E) :=
    ⟨f,memℓp_infty ⟨M,by rintro _ ⟨p,rfl⟩; exact hf p⟩⟩
  let glp : BoundedFunctions (X := X) (E := E) :=
    ⟨g,memℓp_infty ⟨M,by rintro _ ⟨p,rfl⟩; exact hg p⟩⟩
  have hb : ‖flp-glp‖ ≤ q*‖flp-glp‖ := by
    apply lp.norm_le_of_forall_le (mul_nonneg hq (norm_nonneg _))
    apply hstep _ (norm_nonneg _)
    intro p
    change ‖(flp-glp) p‖ ≤ ‖flp-glp‖
    exact lp.norm_apply_le_norm (by norm_num : (∞ : ℝ≥0∞) ≠ 0) _ p
  have hz : ‖flp-glp‖ = 0 := by nlinarith [norm_nonneg (flp-glp)]
  funext p
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hp := lp.norm_apply_le_norm (by norm_num : (∞ : ℝ≥0∞) ≠ 0) (flp-glp) p
  change ‖f p-g p‖ ≤ ‖flp-glp‖ at hp
  rw [hz] at hp
  exact le_antisymm hp (norm_nonneg _)

end SHEStochastic.BoundedMeasurableFixedPoint
