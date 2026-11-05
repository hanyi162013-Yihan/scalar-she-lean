module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.BesselSynthesis

open scoped ENNReal
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def vector (a : ι → E) (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (x : E) : lp (fun _ : ι => 𝕜) 2 :=
  ⟨fun i => inner 𝕜 (a i) x, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs x)⟩

theorem vector_norm_sq (a : ι → E) (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (x : E) : ‖vector a hs x‖ ^ 2 = ∑' i, ‖inner 𝕜 (a i) x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (vector a hs x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, vector] using h

def analysisLinear (a : ι → E) (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2)) :
    E →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2 where
  toFun := vector a hs
  map_add' x y := by
    apply lp.ext
    funext i
    change inner 𝕜 (a i) (x + y) = inner 𝕜 (a i) x + inner 𝕜 (a i) y
    exact inner_add_right _ _ _
  map_smul' c x := by apply lp.ext; funext i; simp [vector, inner_smul_right]

def analysis (a : ι → E) (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (U : ℝ) (hU : 0 ≤ U)
    (hb : ∀ x : E, (∑' i, ‖inner 𝕜 (a i) x‖ ^ 2) ≤ U * ‖x‖ ^ 2) :
    E →L[𝕜] lp (fun _ : ι => 𝕜) 2 :=
  (analysisLinear a hs).mkContinuous (Real.sqrt U) (fun x => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg U) (norm_nonneg x))).mp
    rw [mul_pow, Real.sq_sqrt hU]
    change ‖vector a hs x‖ ^ 2 ≤ _
    rw [vector_norm_sq]
    exact hb x)

@[simp] theorem analysis_apply (a : ι → E)
    (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (U : ℝ) (hU : 0 ≤ U) (hb : ∀ x : E, (∑' i, ‖inner 𝕜 (a i) x‖ ^ 2) ≤ U * ‖x‖ ^ 2)
    (x : E) (i : ι) : analysis a hs U hU hb x i = inner 𝕜 (a i) x := rfl

def synthesis [CompleteSpace E] (a : ι → E) (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (U : ℝ) (hU : 0 ≤ U)
    (hb : ∀ x : E, (∑' i, ‖inner 𝕜 (a i) x‖ ^ 2) ≤ U * ‖x‖ ^ 2) :
    lp (fun _ : ι => 𝕜) 2 →L[𝕜] E := (analysis a hs U hU hb).adjoint

@[simp] theorem synthesis_single [CompleteSpace E] [DecidableEq ι] (a : ι → E)
    (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (U : ℝ) (hU : 0 ≤ U) (hb : ∀ x : E, (∑' i, ‖inner 𝕜 (a i) x‖ ^ 2) ≤ U * ‖x‖ ^ 2)
    (i : ι) : synthesis a hs U hU hb (lp.single 2 i 1) = a i := by
  apply ext_inner_right 𝕜
  intro x
  rw [synthesis, ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left]
  simp [RCLike.inner_apply]

theorem analysis_norm_sq (a : ι → E)
    (hs : ∀ x : E, Summable (fun i => ‖inner 𝕜 (a i) x‖ ^ 2))
    (U : ℝ) (hU : 0 ≤ U) (hb : ∀ x : E, (∑' i, ‖inner 𝕜 (a i) x‖ ^ 2) ≤ U * ‖x‖ ^ 2)
    (x : E) : ‖analysis a hs U hU hb x‖ ^ 2 = ∑' i, ‖inner 𝕜 (a i) x‖ ^ 2 :=
  vector_norm_sq a hs x

end SHE.BesselSynthesis
