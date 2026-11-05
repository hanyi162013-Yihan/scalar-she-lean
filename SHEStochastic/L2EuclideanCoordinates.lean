module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.L2EuclideanCoordinates

open MeasureTheory Finset
open scoped ENNReal

variable {X d : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype d] [DecidableEq d]

abbrev Physical := Lp (EuclideanSpace ℝ d) 2 μ
abbrev Components := PiLp 2 (fun _ : d => Lp ℝ 2 μ)

def projection (i : d) : EuclideanSpace ℝ d →L[ℝ] ℝ := PiLp.proj 2 _ i

def injection (i : d) : ℝ →L[ℝ] EuclideanSpace ℝ d :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)

def coordinates : Physical (d := d) μ →L[ℝ] Components (d := d) μ :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (projection i).compLpL 2 μ))

theorem coordinates_ae (u : Physical (d := d) μ) :
    ∀ᵐ x ∂μ, ∀ i, coordinates μ u i x = u x i := by
  apply ae_all_iff.mpr
  intro i
  exact (projection i).coeFn_compLpL u

def reconstruction : Components (d := d) μ →L[ℝ] Physical (d := d) μ :=
  ∑ i, ((injection i).compLpL 2 μ).comp (PiLp.proj 2 _ i)

theorem reconstruction_ae (u : Components (d := d) μ) :
    ⇑(reconstruction μ u) =ᵐ[μ] fun x => ∑ i, injection i (u i x) := by
  have hc : reconstruction μ u = ∑ i, (injection i).compLpL 2 μ (u i) := by
    simp only [reconstruction, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply]
  rw [hc]
  have hi : ∀ᵐ x ∂μ, ∀ i : d,
      ((injection i).compLpL 2 μ (u i)) x = injection i (u i x) :=
    ae_all_iff.mpr (fun i => (injection i).coeFn_compLpL (u i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => (injection i).compLpL 2 μ (u i)), hi] with x hs hi
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hi i)

theorem reconstruct_coordinates (u : Physical (d := d) μ) :
    reconstruction μ (coordinates μ u) = u := by
  apply Lp.ext
  filter_upwards [reconstruction_ae μ (coordinates μ u), coordinates_ae μ u] with x hr hc
  rw [hr]
  ext i
  simp [injection, hc, Pi.single_apply]

theorem coordinates_reconstruct (u : Components (d := d) μ) :
    coordinates μ (reconstruction μ u) = u := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [coordinates_ae μ (reconstruction μ u), reconstruction_ae μ u] with x hc hr
  rw [hc, hr]
  simp [injection, Pi.single_apply]

theorem inner_coordinates (u v : Physical (d := d) μ) :
    inner ℝ (coordinates μ u) (coordinates μ v) = inner ℝ u v := by
  rw [PiLp.inner_apply, L2.inner_def]
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜 := ℝ)
    (coordinates μ u i) (coordinates μ v i))]
  apply integral_congr_ae
  filter_upwards [coordinates_ae μ u, coordinates_ae μ v] with x hu hv
  simp only [hu, hv, PiLp.inner_apply]

/-- The actual vector-valued `L²` space is the finite Hilbert sum of its
scalar coordinate spaces, with exactly the same norm. -/
def equivalence : Physical (d := d) μ ≃ₗᵢ[ℝ] Components (d := d) μ :=
  LinearIsometryEquiv.ofSurjective
    { (coordinates μ).toLinearMap with
      norm_map' := fun u => by
        have hh := inner_coordinates μ u u
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hh
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh }
    (fun u => ⟨reconstruction μ u, coordinates_reconstruct μ u⟩)

theorem equivalence_apply (u : Physical (d := d) μ) : equivalence μ u = coordinates μ u := rfl

theorem equivalence_symm (u : Components (d := d) μ) :
    (equivalence μ).symm u = reconstruction μ u := by
  apply (equivalence μ).injective
  exact (equivalence μ).apply_symm_apply u |>.trans (coordinates_reconstruct μ u).symm

end SHEStochastic.L2EuclideanCoordinates
