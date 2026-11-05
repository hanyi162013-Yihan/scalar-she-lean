module

public import SHEStochastic.MatrixHaarNoiseRotation
public import SHEStochastic.MeasurableHilbertSynthesis
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHaarParameterColumns
open MeasureTheory Matrix MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d P : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace P]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩

theorem continuous_indicator (s : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) :
    Continuous (fun v : EuclideanSpace ℝ d => indicatorConstLp 2 hs (measure_ne_top μ s) v) := by
  let C := (μ).real s ^ (1/(2 : ENNReal).toReal)
  have hC : 0 ≤ C := Real.rpow_nonneg (measureReal_nonneg) _
  apply LipschitzWith.continuous (K := ⟨C, hC⟩)
  rw [lipschitzWith_iff_dist_le_mul]
  intro v w
  calc
    _ = ‖indicatorConstLp 2 hs (measure_ne_top μ s) (v-w)‖ := by
      rw [dist_eq_norm, indicatorConstLp_sub]
    _ = ‖v-w‖*C := norm_indicatorConstLp (by norm_num) (by norm_num)
    _ ≤ _ := by change ‖v-w‖*C ≤ C*dist v w; rw [dist_eq_norm, mul_comm]

theorem detail_indicators (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (s t : Set (AddCircle (1 : ℝ))) (hs : MeasurableSet s) (ht : MeasurableSet t) (i : d) :
    MatrixHaarLpColumns.vector μ κ s t hs ht i=
      indicatorConstLp 2 hs (measure_ne_top μ s)
        (MatrixHaarRootColumns.column (MatrixHaarAlgebra.left (MatrixHaarFunctions.mass μ κ s)
          (MatrixHaarFunctions.mass μ κ t)) i)+
      indicatorConstLp 2 ht (measure_ne_top μ t)
        (MatrixHaarRootColumns.column (MatrixHaarAlgebra.right (MatrixHaarFunctions.mass μ κ s)
          (MatrixHaarFunctions.mass μ κ t)) i) := by
  apply Lp.ext
  let L := MatrixHaarRootColumns.column (MatrixHaarAlgebra.left (MatrixHaarFunctions.mass μ κ s)
    (MatrixHaarFunctions.mass μ κ t)) i
  let R := MatrixHaarRootColumns.column (MatrixHaarAlgebra.right (MatrixHaarFunctions.mass μ κ s)
    (MatrixHaarFunctions.mass μ κ t)) i
  filter_upwards [MatrixHaarLpColumns.vector_ae μ κ s t hs ht i,
    Lp.coeFn_add (indicatorConstLp 2 hs (measure_ne_top μ s) L)
      (indicatorConstLp 2 ht (measure_ne_top μ t) R),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := L),
    indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := measure_ne_top μ t) (c := R)] with x hv ha hl hr
  rw [hv, ha, Pi.add_apply, hl, hr]
  change MatrixHaarRootColumns.column (MatrixHaarFunctions.column μ κ s t x) i=_
  change MatrixHaarRootColumns.columnMap i
    ((s.indicator (fun _ => MatrixHaarAlgebra.left (MatrixHaarFunctions.mass μ κ s)
      (MatrixHaarFunctions.mass μ κ t)) x)+
      t.indicator (fun _ => MatrixHaarAlgebra.right (MatrixHaarFunctions.mass μ κ s)
        (MatrixHaarFunctions.mass μ κ t)) x)=_
  by_cases hxs : x∈s <;> by_cases hxt : x∈t <;>
    simp [hxs, hxt, map_add, map_zero, L, R]

theorem mass_measurable (K : P × AddCircle (1 : ℝ) → Matrix d d ℝ) (hK : Measurable K)
    (s : Set (AddCircle (1 : ℝ))) :
    Measurable (fun p => MatrixHaarFunctions.mass μ (fun x => K (p,x)) s) :=
  (hK.stronglyMeasurable.integral_prod_right' (ν := (μ).restrict s)).measurable

/-- Actual countable weighted Haar columns are Borel functions of
any jointly measurable matrix covariance profile. -/
theorem column (Q : P → Profile d)
    (hQ : Measurable (fun z : P × AddCircle (1 : ℝ) => (Q z.1).value z.2))
    (k : d × SHE.FiniteHaar.HaarNode) : Measurable (fun p => MatrixInfiniteHaar.column (Q p) k) := by
  cases k with
  | mk i q =>
    cases q with
    | none =>
      have hm := mass_measurable _ hQ Set.univ
      simp only [MatrixHaarFunctions.mass, Measure.restrict_univ] at hm
      have hc := MatrixHaarMeasurability.measurable_inverse.comp (CFC.measurable_sqrt.comp hm)
      have hv := (MatrixHaarRootColumns.columnMap i).continuous.measurable.comp hc
      have hi := (continuous_indicator (d := d) Set.univ MeasurableSet.univ).measurable.comp hv
      convert! hi using 1
      funext p
      change MatrixHaarRootColumns.constant μ (MatrixFiniteHaar.inverseSqrt (∫ y, (Q p).value y ∂μ)) i=
        indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ)
          (MatrixHaarRootColumns.column (MatrixFiniteHaar.inverseSqrt (∫ y, (Q p).value y ∂μ)) i)
      apply Lp.ext
      filter_upwards [MatrixHaarRootColumns.constant_ae μ _ i,
        indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ) (hμs := measure_ne_top μ Set.univ)
          (c := MatrixHaarRootColumns.column (MatrixFiniteHaar.inverseSqrt (∫ y, (Q p).value y ∂μ)) i)] with x hroot hind
      exact hroot.trans (by simpa only [Set.indicator_univ] using hind.symm)
    | some p =>
      let s := MatrixGlobalHaar.child p false
      let t := MatrixGlobalHaar.child p true
      have hs := MatrixGlobalHaar.child_measurable p false
      have ht := MatrixGlobalHaar.child_measurable p true
      have hm := (mass_measurable _ hQ s).prodMk (mass_measurable _ hQ t)
      have hc := MatrixHaarMeasurability.measurable_children.comp hm
      have hl := (MatrixHaarRootColumns.columnMap i).continuous.measurable.comp hc.fst
      have hr := (MatrixHaarRootColumns.columnMap i).continuous.measurable.comp hc.snd
      have hi := ((continuous_indicator s hs).measurable.comp hl).add
        ((continuous_indicator t ht).measurable.comp hr)
      convert! hi using 1
      funext x
      exact detail_indicators (Q x).value s t hs ht i

end SHEStochastic.MatrixHaarParameterColumns
