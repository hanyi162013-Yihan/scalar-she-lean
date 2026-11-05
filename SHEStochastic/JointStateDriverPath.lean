module

public import SHEStochastic.PastedCylinderMartingale
public import SHE.CanonicalContinuousStateDriver
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.JointStateDriverPath
open MeasureTheory ProbabilityTheory StoppedPathPasting
open scoped NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Countable ι] (H : ℝ≥0)

/-- The countable driver is retained with the state. The product topology
requires no artificial norm or summability assumption on Brownian paths. -/
abbrev State (E ι : Type*) := E × (ι → ℝ)

def pack (x : SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    Path H (State E ι) :=
  ⟨fun t ↦ (x.1 t, fun i ↦ x.2 i t),
    x.1.continuous.prodMk (continuous_pi fun i ↦ (x.2 i).continuous)⟩

def unpack (x : Path H (State E ι)) :
    SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H :=
  (⟨fun t ↦ (x t).1, continuous_fst.comp x.continuous⟩,
    fun i ↦ ⟨fun t ↦ (x t).2 i, (continuous_apply i).comp (continuous_snd.comp x.continuous)⟩)

theorem continuous_pack : Continuous (pack (E := E) (ι := ι) H) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
    (continuous_pi fun i ↦ continuous_eval.comp
      (((continuous_apply i).comp continuous_fst.snd).prodMk continuous_snd))

theorem continuous_unpack : Continuous (unpack (E := E) (ι := ι) H) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_fst.comp continuous_eval
  · apply continuous_pi
    intro i
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_apply i).comp (continuous_snd.comp continuous_eval)

theorem measurable_pack : Measurable (pack (E := E) (ι := ι) H) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval t).comp measurable_fst).prodMk
    (measurable_pi_iff.mpr fun i ↦ (ContinuousMap.measurable_eval t).comp
      ((measurable_pi_apply i).comp measurable_snd))

theorem measurable_unpack : Measurable (unpack (E := E) (ι := ι) H) := by
  apply Measurable.prodMk
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact measurable_fst.comp (ContinuousMap.measurable_eval t)
  · apply measurable_pi_iff.mpr
    intro i
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (measurable_pi_apply i).comp
      (measurable_snd.comp (ContinuousMap.measurable_eval t))

/-- The new joint path presentation is measurably equivalent to the
existing canonical state/driver space. Existing conditional-law tools
and the general pasting theorem therefore use the same sample space. -/
def equiv : SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H ≃ᵐ
    Path H (State E ι) where
  toFun := pack H
  invFun := unpack H
  left_inv x := by
    apply Prod.ext
    · exact ContinuousMap.ext (fun _ ↦ rfl)
    · funext i
      exact ContinuousMap.ext (fun _ ↦ rfl)
  right_inv x := ContinuousMap.ext (fun _ ↦ rfl)
  measurable_toFun := measurable_pack H
  measurable_invFun := measurable_unpack H

theorem state_paste (r : Time H) (x y : Path H (State E ι)) :
    (unpack H (paste H r x y)).1 = paste H r (unpack H x).1 (unpack H y).1 := by
  ext t
  rfl

theorem driver_paste (r : Time H) (x y : Path H (State E ι)) (i : ι) :
    (unpack H (paste H r x y)).2 i = paste H r ((unpack H x).2 i) ((unpack H y).2 i) := by
  ext t
  rfl

/-- A fresh driver starts at zero. Translate it by the driver value at
the joining time, leaving its increments and the state path unchanged. -/
def restart (d : ι → ℝ)
    (x : SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    Path H (State E ι) :=
  ⟨fun t ↦ (x.1 t, fun i ↦ d i + x.2 i t),
    x.1.continuous.prodMk (continuous_pi fun i ↦ continuous_const.add (x.2 i).continuous)⟩

theorem measurable_restart : Measurable (fun p : (ι → ℝ) ×
    SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H ↦ restart H p.1 p.2) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval t).comp measurable_snd.fst).prodMk
    (measurable_pi_iff.mpr fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).add
        ((ContinuousMap.measurable_eval t).comp ((measurable_pi_apply i).comp measurable_snd.snd)))

/-- Lift an initial-state kernel to the joint state/driver space. -/
def continuationKernel
    (κ : Kernel E (SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H))
    [IsMarkovKernel κ] : Kernel (State E ι) (Path H (State E ι)) :=
  ((Kernel.deterministic Prod.snd measurable_snd) ×ₖ κ.prodMkRight (ι → ℝ)).map
    (fun p ↦ restart H p.1 p.2)

instance (κ : Kernel E (SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H))
    [IsMarkovKernel κ] : IsMarkovKernel (continuationKernel H κ) := by
  unfold continuationKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_restart H)

theorem continuationKernel_apply
    (κ : Kernel E (SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H))
    [IsMarkovKernel κ] (z : State E ι) :
    continuationKernel H κ z = (κ z.1).map (restart H z.2) := by
  rw [continuationKernel, Kernel.map_apply _ (measurable_restart H), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.prodMkRight_apply, Measure.dirac_prod,
    Measure.map_map (measurable_restart H) measurable_prodMk_left]
  rfl

theorem continuationKernel_initial
    (κ : Kernel E (SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H))
    [IsMarkovKernel κ] (z : State E ι)
    (hstate : ∀ᵐ x ∂κ z.1, x.1 (origin H) = z.1)
    (hdriver : ∀ᵐ x ∂κ z.1, ∀ i, x.2 i (origin H) = 0) :
    ∀ᵐ y ∂continuationKernel H κ z, y (origin H) = z := by
  rw [continuationKernel_apply]
  have hm : Measurable (restart (E := E) H z.2) :=
    (measurable_restart H).comp (measurable_const.prodMk measurable_id)
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval (origin H)) measurable_const)).mpr
  filter_upwards [hstate, hdriver] with x hx hd
  apply Prod.ext hx
  funext i
  simp [restart, hd i]

end SHEStochastic.JointStateDriverPath
