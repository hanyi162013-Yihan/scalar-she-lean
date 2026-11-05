module

public import SHE.WeightedHilbertSum
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.InputProjection
open scoped ENNReal InnerProductSpace

variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def weightedEnergy (b : HilbertBasis I ℂ E) (w : I → ℝ) (f : E) :=
  ∑' i, w i*‖b.repr f i‖^2

omit [CompleteSpace E] in
/-- Weighted Fourier duality is proved on actual ℓ² vectors. The
negative input remains inside its own signed Fourier energy. -/
theorem weighted_cauchy (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0<w i)
    (f g : E)
    (hf : Summable (fun i => (w i)⁻¹*‖b.repr f i‖^2))
    (hg : Summable (fun i => w i*‖b.repr g i‖^2)) :
    ‖inner ℂ f g‖^2 ≤ weightedEnergy b (fun i => (w i)⁻¹) f*weightedEnergy b w g := by
  let U := WeightedHilbertSum.vector w (fun i => (hw i).le) (b.repr g) hg
  let V := WeightedHilbertSum.vector (fun i => (w i)⁻¹) (fun i => inv_nonneg.mpr (hw i).le) (b.repr f) hf
  have he : inner ℂ V U = inner ℂ f g := by
    rw [lp.inner_eq_tsum,← b.repr.inner_map_map,lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change inner ℂ ((Real.sqrt ((w i)⁻¹):ℂ) • b.repr f i)
      ((Real.sqrt (w i):ℂ) • b.repr g i) = inner ℂ (b.repr f i) (b.repr g i)
    rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal,← mul_assoc]
    have hp : Real.sqrt ((w i)⁻¹)*Real.sqrt (w i)=1 := by
      rw [Real.sqrt_inv,inv_mul_cancel₀ (Real.sqrt_pos.mpr (hw i)).ne']
    rw [← Complex.ofReal_mul,hp,Complex.ofReal_one,one_mul]
  have hb := pow_le_pow_left₀ (norm_nonneg (inner ℂ V U)) (norm_inner_le_norm (𝕜:=ℂ) V U) 2
  rw [he,mul_pow] at hb
  simpa only [U,V,WeightedHilbertSum.vector_norm_sq,weightedEnergy] using hb

omit [CompleteSpace E] in
/-- A positive inverse inequality on a genuine orthogonal-projection
range gives the corresponding negative-norm bound on the input. -/
theorem projection_bound (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0<w i)
    (S : Submodule ℂ E) [S.HasOrthogonalProjection] (C : ℝ) (hC : 0≤C)
    (hfinite : ∀ g : S, Summable (fun i => w i*‖b.repr (g:E) i‖^2))
    (hinverse : ∀ g : S, weightedEnergy b w (g:E) ≤ C*‖(g:E)‖^2)
    (f : E) (hf : Summable (fun i => (w i)⁻¹*‖b.repr f i‖^2)) :
    ‖S.starProjection f‖^2 ≤ C*weightedEnergy b (fun i => (w i)⁻¹) f := by
  let g : S := S.orthogonalProjectionOnto f
  have hg : (g:E)=S.starProjection f := rfl
  have he : ‖inner ℂ f (g:E)‖=‖(g:E)‖^2 := by
    have hi := S.inner_orthogonalProjectionOnto_eq_of_mem_right g f
    change inner ℂ (g:E) (g:E)=inner ℂ f (g:E) at hi
    rw [← hi,inner_self_eq_norm_sq_to_K,norm_pow]
    simp only [RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
  have hc := weighted_cauchy b w hw f (g:E) hf (hfinite g)
  rw [he] at hc
  have hE : 0≤weightedEnergy b (fun i => (w i)⁻¹) f :=
    tsum_nonneg (fun i => mul_nonneg (inv_nonneg.mpr (hw i).le) (sq_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (hinverse g) hE
  by_cases hz : ‖(g:E)‖^2=0
  · rw [← hg,hz]
    exact mul_nonneg hC hE
  · have hp : 0<‖(g:E)‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    have hh : ‖(g:E)‖^2*‖(g:E)‖^2 ≤
        (C*weightedEnergy b (fun i => (w i)⁻¹) f)*‖(g:E)‖^2 := by
      nlinarith only [hc,hm]
    rw [← hg]
    exact (mul_le_mul_iff_left₀ hp).mp hh

section RealProjection
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

omit [CompleteSpace E] in
/-- The same duality applies to actual real-valued step subspaces of
a complex Fourier Hilbert space; no complexification of the projection
or unjustified change of its range is needed. -/
theorem real_projection_bound (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0<w i)
    (S : Submodule ℝ E) [S.HasOrthogonalProjection] (C : ℝ) (hC : 0≤C)
    (hfinite : ∀ g : S, Summable (fun i => w i*‖b.repr (g:E) i‖^2))
    (hinverse : ∀ g : S, weightedEnergy b w (g:E) ≤ C*‖(g:E)‖^2)
    (f : E) (hf : Summable (fun i => (w i)⁻¹*‖b.repr f i‖^2)) :
    ‖S.starProjection f‖^2 ≤ C*weightedEnergy b (fun i => (w i)⁻¹) f := by
  let g : S := S.orthogonalProjectionOnto f
  have hg : (g:E)=S.starProjection f := rfl
  have he : ‖(g:E)‖^2 ≤ ‖inner ℂ f (g:E)‖ := by
    have hi := S.inner_orthogonalProjectionOnto_eq_of_mem_right g f
    change inner ℝ (g:E) (g:E)=inner ℝ f (g:E) at hi
    rw [real_inner_self_eq_norm_sq,real_inner_eq_re_inner ℂ] at hi
    rw [hi]
    exact Complex.re_le_norm _
  have hc := weighted_cauchy b w hw f (g:E) hf (hfinite g)
  have hc' := pow_le_pow_left₀ (sq_nonneg ‖(g:E)‖) he 2
  have hE : 0≤weightedEnergy b (fun i => (w i)⁻¹) f :=
    tsum_nonneg (fun i => mul_nonneg (inv_nonneg.mpr (hw i).le) (sq_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (hinverse g) hE
  by_cases hz : ‖(g:E)‖^2=0
  · rw [← hg,hz]
    exact mul_nonneg hC hE
  · have hp : 0<‖(g:E)‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    have hh : ‖(g:E)‖^2*‖(g:E)‖^2 ≤
        (C*weightedEnergy b (fun i => (w i)⁻¹) f)*‖(g:E)‖^2 := by
      nlinarith only [hc',hc,hm]
    rw [← hg]
    exact (mul_le_mul_iff_left₀ hp).mp hh

end RealProjection

omit [CompleteSpace E] in
/-- A single genuine coarse average needs only its exact energy
pairing identity, not a prior identification of the entire projection.
The massive negative-input estimate is then a conclusion of duality. -/
theorem single_vector_bound (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0<w i)
    (f g : E) (C : ℝ) (hC : 0≤C)
    (hf : Summable (fun i => (w i)⁻¹*‖b.repr f i‖^2))
    (hg : Summable (fun i => w i*‖b.repr g i‖^2))
    (hpair : (inner ℂ f g).re=‖g‖^2)
    (hinverse : weightedEnergy b w g ≤ C*‖g‖^2) :
    ‖g‖^2 ≤ C*weightedEnergy b (fun i => (w i)⁻¹) f := by
  have he : ‖g‖^2 ≤ ‖inner ℂ f g‖ := by rw [← hpair]; exact Complex.re_le_norm _
  have hc := weighted_cauchy b w hw f g hf hg
  have hc' := pow_le_pow_left₀ (sq_nonneg ‖g‖) he 2
  have hE : 0≤weightedEnergy b (fun i => (w i)⁻¹) f :=
    tsum_nonneg (fun i => mul_nonneg (inv_nonneg.mpr (hw i).le) (sq_nonneg _))
  have hm := mul_le_mul_of_nonneg_left hinverse hE
  by_cases hz : ‖g‖^2=0
  · rw [hz]
    exact mul_nonneg hC hE
  · have hp : 0<‖g‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    have hh : ‖g‖^2*‖g‖^2 ≤
        (C*weightedEnergy b (fun i => (w i)⁻¹) f)*‖g‖^2 := by
      nlinarith only [hc',hc,hm]
    exact (mul_le_mul_iff_left₀ hp).mp hh

end SHE.InputProjection
