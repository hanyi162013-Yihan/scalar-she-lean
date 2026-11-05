module

public import SHE.LpEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.IndicatorSections
open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {X P E : Type*} [MeasurableSpace X] [MeasurableSpace P]
  [NormedAddCommGroup E] (μ : Measure P) [IsFiniteMeasure μ]

def sectionLp (s : Set (X × P)) (hs : MeasurableSet s) (c : E) (x : X) : Lp E 2 μ :=
  indicatorConstLp 2 (measurable_prodMk_left (x := x) hs) (measure_ne_top μ _) c

theorem sectionLp_congr {s t : Set (X × P)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s = t) (c : E) : sectionLp μ s hs c = sectionLp μ t ht c := by
  subst t
  rfl

theorem sectionLp_ae (s : Set (X × P)) (hs : MeasurableSet s) (c : E) (x : X) :
    sectionLp μ s hs c x =ᵐ[μ] (Prod.mk x ⁻¹' s).indicator (fun _ => c) :=
  indicatorConstLp_coeFn

theorem sectionLp_empty (c : E) (x : X) : sectionLp μ ∅ MeasurableSet.empty c x = 0 :=
  indicatorConstLp_empty

@[simp] theorem sectionLp_empty_fun (c : E) : sectionLp (X := X) μ ∅ MeasurableSet.empty c = 0 := by
  funext x
  exact sectionLp_empty μ c x

theorem sectionLp_union {s t : Set (X × P)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hd : Disjoint s t) (c : E) :
    sectionLp μ (s ∪ t) (hs.union ht) c = sectionLp μ s hs c + sectionLp μ t ht c := by
  funext x
  exact indicatorConstLp_disjoint_union (measurable_prodMk_left hs) (measurable_prodMk_left ht)
    (measure_ne_top μ _) (measure_ne_top μ _) (hd.preimage (Prod.mk x)) c

theorem sectionLp_compl {s : Set (X × P)} (hs : MeasurableSet s) (c : E) :
    sectionLp μ sᶜ hs.compl c = fun x => Lp.const 2 μ c - sectionLp μ s hs c x := by
  funext x
  apply Lp.ext
  filter_upwards [sectionLp_ae μ sᶜ hs.compl c x, sectionLp_ae μ s hs c x,
    Lp.coeFn_const 2 μ c, Lp.coeFn_sub (Lp.const 2 μ c) (sectionLp μ s hs c x)]
    with p hc hrep hconst hsub
  rw [hsub]
  change sectionLp μ sᶜ _ c x p = Lp.const 2 μ c p - sectionLp μ s _ c x p
  rw [hconst, hc, hrep]
  by_cases h : (x, p) ∈ s <;> simp [h]

/-- Monotone unions of measurable sets converge in L² by the existing
indicator-norm formula and continuity of a finite measure. -/
theorem tendsto_indicator_iUnion (s : ℕ → Set P) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (c : E) :
    Tendsto (fun n => indicatorConstLp 2 (hs n) (measure_ne_top μ _) c) atTop
      (𝓝 (indicatorConstLp 2 (MeasurableSet.iUnion hs) (measure_ne_top μ _) c)) := by
  apply tendsto_indicatorConstLp_set (by simp)
  let d (n : ℕ) := (⋃ i, s i) \ s n
  have hd (n : ℕ) : MeasurableSet (d n) := (MeasurableSet.iUnion hs).diff (hs n)
  have hanti : Antitone d := fun i j hij => sdiff_subset_sdiff_right (hm hij)
  have hempty : ⋂ n, d n = ∅ := by
    ext p
    simp only [d, mem_iInter, Set.mem_sdiff, mem_iUnion, mem_empty_iff_false, iff_false]
    rintro h
    obtain ⟨i, hi⟩ := (h 0).1
    exact (h i).2 hi
  have hlim := tendsto_measure_iInter_atTop (fun n => (hd n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  simp only [hempty, measure_empty] at hlim
  convert hlim using 1
  funext n
  rw [symmDiff_of_le (subset_iUnion s n)]
  rfl

/-- A measurable product-set has a strongly measurable family of L²
indicator sections, without separability of the whole L² space. -/
theorem stronglyMeasurable_sectionLp (s : Set (X × P)) (hs : MeasurableSet s) (c : E) :
    StronglyMeasurable (sectionLp μ s hs c) := by
  classical
  induction s, hs using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
  | empty =>
    rw [sectionLp_empty_fun]
    exact stronglyMeasurable_zero
  | basic s hs =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    have heq : sectionLp μ (a ×ˢ b) (ha.prod hb) c =
        a.indicator (fun _ => indicatorConstLp 2 hb (measure_ne_top μ _) c) := by
      funext x
      by_cases hx : x ∈ a <;>
        simp only [sectionLp, mk_preimage_prod_right_eq_if, hx, ite_true, ite_false,
          indicatorConstLp_empty, indicator_apply]
    rw [heq]
    exact stronglyMeasurable_const.indicator ha
  | compl s hs ih =>
    rw [sectionLp_compl μ hs c]
    exact stronglyMeasurable_const.sub ih
  | iUnion f hfd hfm ihf =>
    have hfin (s : Finset ℕ) :
        StronglyMeasurable (sectionLp μ (⋃ i ∈ s, f i) (by measurability) c) := by
      induction s using Finset.induction_on with
      | empty =>
        have he := sectionLp_congr μ (s := ⋃ i ∈ (∅ : Finset ℕ), f i)
          (by measurability) MeasurableSet.empty (by simp) c
        rw [he, sectionLp_empty_fun]
        exact stronglyMeasurable_zero
      | @insert a s ha ih =>
        have hd : Disjoint (f a) (⋃ i ∈ s, f i) := by
          apply disjoint_iUnion_right.mpr
          intro i
          apply disjoint_iUnion_right.mpr
          intro hi
          exact hfd (fun h => ha (h ▸ hi))
        have heq : (⋃ i ∈ insert a s, f i) = f a ∪ ⋃ i ∈ s, f i := by simp
        have he := sectionLp_congr μ (s := ⋃ i ∈ insert a s, f i)
          (by measurability) ((hfm a).union (by measurability)) heq c
        rw [he, sectionLp_union μ (hfm a) (by measurability) hd c]
        exact (ihf a).add ih
    let s (n : ℕ) := ⋃ i ∈ Finset.range n, f i
    have hs (n : ℕ) : MeasurableSet (s n) := by measurability
    have hm : Monotone s := fun i j hij =>
      biUnion_subset_biUnion_left (Finset.range_mono hij)
    have hfull : ⋃ n, s n = ⋃ i, f i := by
      ext p
      simp only [s, mem_iUnion]
      constructor
      · rintro ⟨n, i, hi, hp⟩
        exact ⟨i, hp⟩
      · rintro ⟨i, hp⟩
        exact ⟨i + 1, i, Finset.mem_range.mpr (Nat.lt_succ_self i), hp⟩
    apply stronglyMeasurable_of_tendsto atTop (fun n => hfin (Finset.range n))
    apply tendsto_pi_nhds.mpr
    intro x
    have ht := tendsto_indicator_iUnion μ (fun n => Prod.mk x ⁻¹' s n)
      (fun n => measurable_prodMk_left (hs n)) (fun i j hij => preimage_mono (hm hij)) c
    simpa only [← preimage_iUnion, hfull, sectionLp] using ht

end SHEStochastic.IndicatorSections
