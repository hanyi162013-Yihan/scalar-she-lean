module

public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HilbertColumns
open scoped ENNReal
variable {I E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem summable_sq (v : Space I E) : Summable (fun i => ‖v i‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.hasSum_norm (by norm_num : 0 < (2:ENNReal).toReal) v).summable

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

def map (L : E →L[𝕜] F) (v : Space I E) : Space I F :=
  ofSummable (fun i => L (v i))
    (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (v i)) 2
      simpa only [mul_pow] using hh) ((summable_sq v).mul_left (‖L‖^2)))

theorem map_apply (L : E →L[𝕜] F) (v : Space I E) (i : I) : map L v i=L (v i) := rfl

theorem map_norm_le (L : E →L[𝕜] F) (v : Space I E) : ‖map L v‖ ≤ ‖L‖*‖v‖ := by
  have hh : ‖map L v‖^2 ≤ ‖L‖^2*‖v‖^2 := by
    rw [norm_sq,norm_sq,← tsum_mul_left]
    apply (summable_sq (map L v)).tsum_le_tsum _ ((summable_sq v).mul_left (‖L‖^2))
    intro i
    simpa only [map_apply,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (v i)) 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hh)

def mapLinear (L : E →L[𝕜] F) : Space I E →ₗ[𝕜] Space I F where
  toFun := map L
  map_add' v w := by
    apply lp.ext
    funext i
    change L (v i+w i)=L (v i)+L (w i)
    exact map_add L _ _
  map_smul' c v := by
    apply lp.ext
    funext i
    change L (c • v i)=c • L (v i)
    exact map_smul L _ _

def mapCLM (L : E →L[𝕜] F) : Space I E →L[𝕜] Space I F :=
  (mapLinear L).mkContinuous ‖L‖ (map_norm_le L)

theorem mapCLM_apply (L : E →L[𝕜] F) (v : Space I E) (i : I) : mapCLM L v i=L (v i) := rfl

theorem mapCLM_single [DecidableEq I] (L : E →L[𝕜] F) (i : I) (v : E) :
    mapCLM L (lp.single 2 i v)=lp.single 2 i (L v) := by
  apply lp.ext
  funext j
  by_cases hij : i=j
  · subst j
    simp [mapCLM_apply,lp.single_apply,Pi.single]
  · simp [mapCLM_apply,lp.single_apply,Pi.single,Ne.symm hij]

end SHE.HilbertColumns
