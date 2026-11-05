module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.FiniteL2Flatten
open scoped ENNReal

variable {d ι : Type*} [Fintype d]

abbrev Rows := PiLp 2 (fun _ : d => lp (fun _ : ι => ℝ) 2)
abbrev Flat := lp (fun _ : d × ι => ℝ) 2

theorem row_summable (u : Rows (d := d) (ι := ι)) (i : d) :
    Summable (fun q => ‖u i q‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp (u i)).summable (by norm_num : 0 < (2 : ENNReal).toReal)

theorem flat_summable (u : Rows (d := d) (ι := ι)) :
    Summable (fun p : d × ι => ‖u p.1 p.2‖ ^ 2) :=
  (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨row_summable u, ⟨_, hasSum_fintype _⟩⟩

def flatten (u : Rows (d := d) (ι := ι)) : Flat (d := d) (ι := ι) :=
  ⟨fun p => u p.1 p.2, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using flat_summable u)⟩

def linear : Rows (d := d) (ι := ι) →ₗ[ℝ] Flat (d := d) (ι := ι) where
  toFun := flatten
  map_add' u v := by apply lp.ext; funext p; rfl
  map_smul' r u := by apply lp.ext; funext p; rfl

theorem norm_sq (u : Rows (d := d) (ι := ι)) : ‖flatten u‖ ^ 2 = ‖u‖ ^ 2 := by
  have hn (x : lp (fun _ : ι => ℝ) 2) : ‖x‖ ^ 2 = ∑' q, ‖x q‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
  have hf : ‖flatten u‖ ^ 2 = ∑' p : d × ι, ‖u p.1 p.2‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, flatten] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (flatten u)
  rw [hf, (flat_summable u).tsum_prod' (row_summable u), tsum_fintype, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun i _ => (hn (u i)).symm)

def unflatten (u : Flat (d := d) (ι := ι)) : Rows (d := d) (ι := ι) :=
  WithLp.toLp 2 (fun i => ⟨fun q => u (i,q), memℓp_gen (by
    have hs := (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    exact ((summable_prod_of_nonneg (fun p => by positivity)).mp hs).1 i)⟩)

/-- Flattening the finite state index and the infinite noise index
preserves the Hilbert norm exactly. -/
def equivalence : Rows (d := d) (ι := ι) ≃ₗᵢ[ℝ] Flat (d := d) (ι := ι) :=
  LinearIsometryEquiv.ofSurjective
    { linear with norm_map' := fun u =>
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (norm_sq u) }
    (fun u => ⟨unflatten u, by apply lp.ext; funext p; rfl⟩)

theorem equivalence_apply (u : Rows (d := d) (ι := ι)) (i : d) (q : ι) :
    equivalence u (i,q) = u i q := rfl

end SHEStochastic.FiniteL2Flatten
