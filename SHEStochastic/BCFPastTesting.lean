module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Martingale.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.BCFPastTesting
open MeasureTheory
open scoped NNReal ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω]
  [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → X) (hZ : Measurable Z)

include hZ in
/-- Bounded continuous tests of a past variable determine all of its
measurable tests. This is existing L2 density of bounded continuous
functions, pulled back by the actual random variable. -/
theorem setIntegral_zero (Y : Ω → ℝ) (hY : MemLp Y 2 μ)
    (htest : ∀ f : BoundedContinuousFunction X ℝ, (∫ sample, f (Z sample)*Y sample ∂μ) = 0)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.comap Z inferInstance] A) :
    (∫ sample in A, Y sample ∂μ) = 0 := by
  let ν := μ.map Z
  let pull : Lp ℝ 2 ν →ₗᵢ[ℝ] Lp ℝ 2 μ := Lp.compMeasurePreservingₗᵢ ℝ Z ⟨hZ, rfl⟩
  let y : Lp ℝ 2 μ := hY.toLp Y
  let L := (innerSL ℝ y).comp pull.toContinuousLinearMap
  have hd (f : BoundedContinuousFunction X ℝ) : L (BoundedContinuousFunction.toLp 2 ν ℝ f) = 0 := by
    have hp := Lp.coeFn_compMeasurePreserving (BoundedContinuousFunction.toLp 2 ν ℝ f)
      (show MeasurePreserving Z μ ν from ⟨hZ, rfl⟩)
    have hf := (show MeasurePreserving Z μ ν from ⟨hZ, rfl⟩).quasiMeasurePreserving.ae
      (BoundedContinuousFunction.coeFn_toLp 2 ν ℝ f)
    change inner ℝ y (pull _) = 0
    rw [L2.inner_def]
    calc
      _ = ∫ sample, f (Z sample)*Y sample ∂μ := by
        apply integral_congr_ae
        filter_upwards [hY.coeFn_toLp, hp, hf] with sample hy hp hf
        change y sample = Y sample at hy
        change pull (BoundedContinuousFunction.toLp 2 ν ℝ f) sample = _ at hp
        rw [hy, hp]
        dsimp only [Function.comp_apply]
        rw [hf]
        simp only [RCLike.inner_apply, conj_trivial]
      _ = 0 := htest f
  have hL : ∀ u : Lp ℝ 2 ν, L u = 0 := by
    have hh := (BoundedContinuousFunction.toLp_denseRange ℝ ν ℝ (p := 2) (by simp)).equalizer
      L.continuous (continuous_const : Continuous (fun _ : Lp ℝ 2 ν ↦ (0 : ℝ))) (funext hd)
    exact congrFun hh
  obtain ⟨B, hB, rfl⟩ := hA
  let f := B.indicator (fun _ : X ↦ (1 : ℝ))
  have hm : MemLp f 2 ν := (memLp_const (1 : ℝ)).indicator hB.nullMeasurableSet
  let u : Lp ℝ 2 ν := hm.toLp f
  have hp := Lp.coeFn_compMeasurePreserving u (show MeasurePreserving Z μ ν from ⟨hZ, rfl⟩)
  have hf := (show MeasurePreserving Z μ ν from ⟨hZ, rfl⟩).quasiMeasurePreserving.ae hm.coeFn_toLp
  have he : L u = ∫ sample in Z ⁻¹' B, Y sample ∂μ := by
    change inner ℝ y (pull u) = _
    rw [L2.inner_def, ← integral_indicator (hZ hB)]
    apply integral_congr_ae
    filter_upwards [hY.coeFn_toLp, hp, hf] with sample hy hp hf
    change y sample = Y sample at hy
    change pull u sample = u (Z sample) at hp
    change u (Z sample) = f (Z sample) at hf
    rw [hy, hp, hf]
    by_cases h : Z sample ∈ B
    · simp [f, h, RCLike.inner_apply]
    · simp [f, h, RCLike.inner_apply]
  exact he.symm.trans (hL u)

include hZ in
theorem condExp_zero (Y : Ω → ℝ) (hY : MemLp Y 2 μ)
    (htest : ∀ f : BoundedContinuousFunction X ℝ, (∫ sample, f (Z sample)*Y sample ∂μ) = 0) :
    μ[Y | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hZ.comap_le (hY.integrable one_le_two)
    (fun _ _ _ ↦ (integrable_const (0 : ℝ)).integrableOn) (fun A hA _ ↦ ?_)
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  rw [integral_zero]
  exact (setIntegral_zero μ Z hZ Y hY htest hA).symm

/-- Continuous tests of a generating past variable suffice for the
ordinary martingale property on any smaller history filtration. -/
theorem martingale {T : Type*} [Preorder T]
    (F : Filtration T ‹MeasurableSpace Ω›) (past : T → Ω → X)
    (hpast : ∀ t, Measurable (past t))
    (hF : ∀ t, F t ≤ MeasurableSpace.comap (past t) inferInstance)
    (M : T → Ω → ℝ) (ha : StronglyAdapted F M) (hM : ∀ t, MemLp (M t) 2 μ)
    (htest : ∀ s t, s ≤ t → ∀ f : BoundedContinuousFunction X ℝ,
      (∫ sample, f (past s sample)*(M t sample-M s sample) ∂μ) = 0) :
    Martingale M F μ := by
  refine ⟨ha, fun s t hst ↦ ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) ((hM t).integrable one_le_two)
    (fun _ _ _ ↦ ((hM s).integrable one_le_two).integrableOn)
    (fun A hA _ ↦ ?_) (ha s).aestronglyMeasurable).symm
  have hz := setIntegral_zero μ (past s) (hpast s) (fun sample ↦ M t sample-M s sample)
    ((hM t).sub (hM s)) (htest s t hst) (hF s A hA)
  rw [integral_sub ((hM t).integrable one_le_two).integrableOn
    ((hM s).integrable one_le_two).integrableOn] at hz
  exact (sub_eq_zero.mp hz).symm

end SHEStochastic.BCFPastTesting
