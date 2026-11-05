module
public import SHE.OrthogonalItoChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.PairedHilbertIsometry
open OrthogonalItoChannels
variable {A B C D : Type*}
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [NormedAddCommGroup D] [InnerProductSpace ℝ D]

/-- Independent physical/Haar coordinate changes on two orthogonal
channels form one genuine Hilbert isometry. -/
def pair (f : A →ₗᵢ[ℝ] C) (g : B →ₗᵢ[ℝ] D) :
    WithLp 2 (A × B) →ₗᵢ[ℝ] WithLp 2 (C × D) where
  toFun p := WithLp.toLp 2 (f p.fst,g p.snd)
  map_add' p q := by apply WithLp.ofLp_injective; ext <;> simp [map_add]
  map_smul' r p := by apply WithLp.ofLp_injective; ext <;> simp [map_smul]
  norm_map' p := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖f p.fst‖^2+‖g p.snd‖^2 = ‖p.fst‖^2+‖p.snd‖^2
    rw [f.norm_map,g.norm_map]

@[simp] theorem pair_apply (f : A →ₗᵢ[ℝ] C) (g : B →ₗᵢ[ℝ] D) (p : WithLp 2 (A × B)) :
    pair f g p = WithLp.toLp 2 (f p.fst,g p.snd) := rfl

def equivalence (f : A ≃ₗᵢ[ℝ] C) (g : B ≃ₗᵢ[ℝ] D) :
    WithLp 2 (A × B) ≃ₗᵢ[ℝ] WithLp 2 (C × D) :=
  LinearIsometryEquiv.ofSurjective (pair f.toLinearIsometry g.toLinearIsometry) (by
    intro p
    refine ⟨WithLp.toLp 2 (f.symm p.fst,g.symm p.snd),?_⟩
    apply WithLp.ofLp_injective
    ext <;> simp [pair])
end SHE.PairedHilbertIsometry
