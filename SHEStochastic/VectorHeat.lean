module

public import SHEStochastic.L2EuclideanCoordinates
public import SHE.RealHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.VectorHeat
open MeasureTheory SHE SHE.DyadicApproximation

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev Physical := L2EuclideanCoordinates.Physical (d := d) (AddCircle.haarAddCircle (T := (1 : ℝ)))
abbrev Components := L2EuclideanCoordinates.Components (d := d) (AddCircle.haarAddCircle (T := (1 : ℝ)))

def coordinates : Physical (d := d) ≃ₗᵢ[ℝ] Components (d := d) :=
  L2EuclideanCoordinates.equivalence _

def componentMap (t : ℝ) : Components (d := d) →L[ℝ] Components (d := d) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (RealHeat.realHeat t).comp (PiLp.proj 2 _ i)))

theorem componentMap_apply (t : ℝ) (u : Components (d := d)) (i : d) :
    componentMap t u i = RealHeat.realHeat t (u i) := rfl

def heat (t : ℝ) : Physical (d := d) →L[ℝ] Physical (d := d) :=
  coordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((componentMap t).comp coordinates.toContinuousLinearEquiv.toContinuousLinearMap)

theorem coordinate_heat (t : ℝ) (u : Physical (d := d)) (i : d) :
    coordinates (heat t u) i = RealHeat.realHeat t (coordinates u i) := by
  change coordinates (coordinates.symm (componentMap t (coordinates u))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem contraction (t : ℝ) (u : Physical (d := d)) : ‖heat t u‖ ≤ ‖u‖ := by
  rw [← coordinates.norm_map (heat t u), ← coordinates.norm_map u]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i hi
  rw [coordinate_heat]
  exact pow_le_pow_left₀ (norm_nonneg _) (RealHeat.realHeat_contraction t _) 2

theorem zero : heat (d := d) 0 = ContinuousLinearMap.id ℝ (Physical (d := d)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply coordinates.injective
  apply PiLp.ext
  intro i
  rw [coordinate_heat, RealHeat.realHeat_zero]
  rfl

theorem semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heat (d := d) (s+t) = (heat s).comp (heat t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply coordinates.injective
  apply PiLp.ext
  intro i
  change coordinates (heat (s+t) u) i = coordinates (heat s (heat t u)) i
  rw [coordinate_heat, coordinate_heat, coordinate_heat, RealHeat.realHeat_semigroup hs ht]
  rfl

theorem continuous_action : Continuous (fun p : ℝ × Physical (d := d) => heat p.1 p.2) := by
  have hc0 : Continuous (fun p : ℝ × Physical (d := d) =>
      fun i : d => RealHeat.realHeat p.1 (coordinates p.2 i)) := by
    apply continuous_pi
    intro i
    have hi : Continuous (fun u : Physical (d := d) => coordinates u i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => RealL2) i).continuous.comp (coordinates (d := d)).continuous
    have hh : Continuous (fun p : ℝ × Physical (d := d) =>
        (p.1, coordinates p.2 i) : ℝ × Physical (d := d) → ℝ × RealL2) :=
      continuous_fst.prodMk (hi.comp continuous_snd)
    convert! RealHeat.continuous_realHeat_action.comp hh using 1
  have hc : Continuous (fun p : ℝ × Physical (d := d) =>
      componentMap p.1 (coordinates p.2)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => RealL2)).symm.continuous.comp hc0
  convert! (coordinates (d := d)).symm.continuous.comp hc using 1

end SHEStochastic.VectorHeat
