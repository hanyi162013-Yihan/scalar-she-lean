module

public import SHE.ProcessEnergy
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ScaledLpPull
open MeasureTheory Filter
open scoped ENNReal
variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (μ : Measure A) (ν : Measure B) (c : ℝ) (hc : 0<c)
variable (g : A→B) (hg : MeasurePreserving g (ENNReal.ofReal c • μ) ν)
include hg hc

theorem ae_comp {p : B→Prop} (hp : ∀ᵐ y ∂ν,p y) : ∀ᵐ x ∂μ,p (g x) := by
  have hh := hg.quasiMeasurePreserving.ae hp
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp hh

def raw (v : B→E) (x : A) : E := Real.sqrt c • v (g x)

theorem raw_memLp (v : Lp E 2 ν) : MemLp (raw c g v) 2 μ := by
  have hh := (Lp.memLp v).comp_measurePreserving hg
  have hplain : MemLp (v∘g) 2 μ := by
    have hscaled := hh.smul_measure (c := ENNReal.ofReal c⁻¹) ENNReal.ofReal_ne_top
    have heq : ENNReal.ofReal c⁻¹*ENNReal.ofReal c=1 := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr hc).le,inv_mul_cancel₀ hc.ne',ENNReal.ofReal_one]
    simpa only [smul_smul,heq,one_smul] using hscaled
  exact hplain.const_smul (Real.sqrt c)

def pull (v : Lp E 2 ν) : Lp E 2 μ := (raw_memLp μ ν c hc g hg v).toLp (raw c g v)

theorem pull_ae (v : Lp E 2 ν) : pull μ ν c hc g hg v=ᵐ[μ] raw c g v :=
  (raw_memLp μ ν c hc g hg v).coeFn_toLp

omit hg in
theorem raw_norm_sq (v : Lp E 2 ν) (x : A) : ‖raw c g v x‖^2=c*‖v (g x)‖^2 := by
  rw [raw,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hc.le]

variable (he : MeasurableEmbedding g)
include he

theorem pull_norm (v : Lp E 2 ν) : ‖pull μ ν c hc g hg v‖=‖v‖ := by
  have hs : ‖pull μ ν c hc g hg v‖^2=‖v‖^2 := by
    rw [PredictableL2.realLp_norm_sq,PredictableL2.realLp_norm_sq]
    calc
      _ = ∫ x,‖raw c g v x‖^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [pull_ae μ ν c hc g hg v] with x hx
        rw [hx]
      _ = ∫ x,c*‖v (g x)‖^2 ∂μ := by simp_rw [raw_norm_sq (ν := ν) (c := c) (hc := hc) (g := g) v]
      _ = ∫ x,‖v (g x)‖^2 ∂(ENNReal.ofReal c • μ) := by
        rw [integral_const_mul,integral_smul_measure,ENNReal.toReal_ofReal hc.le,smul_eq_mul]
      _ = ∫ y,‖v y‖^2 ∂ν := hg.integral_comp he (fun y : B => ‖v y‖^2)
  nlinarith [norm_nonneg (pull μ ν c hc g hg v),norm_nonneg v]

/-- A true L² pullback with its square-root Jacobian. It applies to
ordinary or predictable sigma algebras and preserves complete-space
norms exactly. -/
def isometry : Lp E 2 ν→ₗᵢ[ℝ] Lp E 2 μ where
  toFun := pull μ ν c hc g hg
  map_add' v w := by
    apply Lp.ext
    have hs := ae_comp μ ν c hc g hg (Lp.coeFn_add v w)
    filter_upwards [pull_ae μ ν c hc g hg (v+w),pull_ae μ ν c hc g hg v,
      pull_ae μ ν c hc g hg w,Lp.coeFn_add (pull μ ν c hc g hg v) (pull μ ν c hc g hg w),hs]
      with x ha hv hw hout hin
    rw [ha,hout]
    simp only [Pi.add_apply]
    rw [hv,hw]
    simp only [raw,hin,Pi.add_apply,smul_add]
  map_smul' r v := by
    apply Lp.ext
    have hs := ae_comp μ ν c hc g hg (Lp.coeFn_smul r v)
    filter_upwards [pull_ae μ ν c hc g hg (r•v),pull_ae μ ν c hc g hg v,
      Lp.coeFn_smul r (pull μ ν c hc g hg v),hs] with x ha hv hout hin
    simp only [RingHom.id_apply]
    rw [ha,hout]
    simp only [Pi.smul_apply]
    rw [hv]
    simp only [raw,hin,Pi.smul_apply,smul_smul]
    congr 1
    exact mul_comm _ _
  norm_map' := pull_norm μ ν c hc g hg he

end SHE.ScaledLpPull
