module

public import SHEStochastic.IndicatorSections
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.LpSections
open MeasureTheory Set Filter TopologicalSpace
open IndicatorSections
open scoped ENNReal Topology

variable {X P E : Type*} [MeasurableSpace X] [MeasurableSpace P]
  [NormedAddCommGroup E] (μ : Measure P) [IsFiniteMeasure μ]

def simpleSection (s : SimpleFunc (X × P) E) (x : X) : Lp E 2 μ :=
  ∑ c ∈ s.range, sectionLp μ (s ⁻¹' {c}) (s.measurableSet_fiber c) c x

theorem simpleSection_measurable (s : SimpleFunc (X × P) E) :
    StronglyMeasurable (simpleSection μ s) :=
  Finset.stronglyMeasurable_fun_sum s.range (fun c _ =>
    stronglyMeasurable_sectionLp μ _ (s.measurableSet_fiber c) c)

theorem simpleSection_ae (s : SimpleFunc (X × P) E) (x : X) :
    simpleSection μ s x =ᵐ[μ] fun p => s (x, p) := by
  classical
  have hr : ∀ᵐ p ∂μ, ∀ c : s.range,
      sectionLp μ (s ⁻¹' {c.val}) (s.measurableSet_fiber c.val) c.val x p =
        (Prod.mk x ⁻¹' (s ⁻¹' {c.val})).indicator (fun _ => c.val) p :=
    ae_all_iff.mpr (fun c => sectionLp_ae μ _ _ c.val x)
  filter_upwards [hr, Lp.coeFn_fun_finsetSum s.range
    (fun c => sectionLp μ (s ⁻¹' {c}) (s.measurableSet_fiber c) c x)] with p hp hsum
  rw [show simpleSection μ s x p = ∑ c ∈ s.range,
      sectionLp μ (s ⁻¹' {c}) (s.measurableSet_fiber c) c x p from hsum]
  calc
    _ = ∑ c ∈ s.range, if s (x, p) = c then c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hp ⟨c, hc⟩]
      rfl
    _ = _ := by simp [s.mem_range_self (x, p)]

/-- Joint strong measurability gives strong measurability into L² when
every section is in L². The ambient L² space need not be separable. -/
theorem stronglyMeasurable_of_joint (K : X → Lp E 2 μ) (raw : X × P → E)
    (hraw : StronglyMeasurable raw) (hK : ∀ x, K x =ᵐ[μ] fun p => raw (x, p)) :
    StronglyMeasurable K := by
  classical
  borelize E
  let S : Set E := Set.range raw ∪ {0}
  letI : SeparableSpace S := hraw.separableSpace_range_union_singleton
  let a (n : ℕ) := SimpleFunc.approxOn raw hraw.measurable S 0 (by simp [S]) n
  apply stronglyMeasurable_of_tendsto atTop (fun n => simpleSection_measurable μ (a n))
  apply tendsto_pi_nhds.mpr
  intro x
  have hm : Measurable (fun p => raw (x, p)) := hraw.measurable.comp measurable_prodMk_left
  have hmem : MemLp (fun p => raw (x, p)) 2 μ := (Lp.memLp (K x)).ae_eq (hK x)
  have hconv := SimpleFunc.tendsto_approxOn_Lp_eLpNorm (p := 2) hm
    (s := S) (y₀ := 0) (by simp [S]) (by simp)
    (Filter.Eventually.of_forall (fun p => subset_closure (show raw (x, p) ∈ S from
      Or.inl (Set.mem_range_self (x, p))))) (by simpa only [MemLp, sub_zero] using hmem)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  convert hconv using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [simpleSection_ae μ (a n) x, hK x] with p ha hKp
  change simpleSection μ (a n) x p - K x p = _
  rw [ha, hKp]
  rfl

end SHEStochastic.LpSections
