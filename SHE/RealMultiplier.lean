module

public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.RealMultiplier
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem mul_memLp (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (v : Lp ℝ 2 μ) :
    MemLp (fun x => c x*v x) 2 μ := by
  apply (Lp.memLp v).of_le_mul (c := U) (hc.mul (Lp.aestronglyMeasurable v))
  filter_upwards [hb] with x hx
  change ‖c x*v x‖ ≤ U*‖v x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def multiply (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (mul_memLp μ c hc U hb v).toLp _

theorem multiply_ae (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (v : Lp ℝ 2 μ) :
    multiply μ c hc U hb v =ᵐ[μ] fun x => c x*v x :=
  (mul_memLp μ c hc U hb v).coeFn_toLp

def linear (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := multiply μ c hc U hb
  map_add' v w := by
    apply Lp.ext
    filter_upwards [multiply_ae μ c hc U hb (v+w),multiply_ae μ c hc U hb v,
      multiply_ae μ c hc U hb w,Lp.coeFn_add v w,
      Lp.coeFn_add (multiply μ c hc U hb v) (multiply μ c hc U hb w)] with x ha hv hw hs ht
    rw [ha,ht]
    simp only [Pi.add_apply,hv,hw,hs,mul_add]
  map_smul' r v := by
    apply Lp.ext
    filter_upwards [multiply_ae μ c hc U hb (r • v),multiply_ae μ c hc U hb v,
      Lp.coeFn_smul r v,Lp.coeFn_smul r (multiply μ c hc U hb v)] with x ha hv hs ht
    simp only [RingHom.id_apply]
    rw [ha,ht]
    simp only [Pi.smul_apply,smul_eq_mul,hv,hs]
    ring

theorem multiply_norm_le (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (v : Lp ℝ 2 μ) :
    ‖multiply μ c hc U hb v‖ ≤ U*‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae μ c hc U hb v,hb] with x hx hb
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- Actual multiplication on literal real `L²`, with no choice of
complex realization or spatial basis. -/
def operator (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (linear μ c hc U hb).mkContinuous U (multiply_norm_le μ c hc U hb)

theorem operator_ae (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (v : Lp ℝ 2 μ) :
    operator μ c hc U hb v =ᵐ[μ] fun x => c x*v x := multiply_ae μ c hc U hb v

theorem operator_symmetric (c : X → ℝ) (hc : AEStronglyMeasurable c μ) (U : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (v w : Lp ℝ 2 μ) :
    ⟪operator μ c hc U hb v,w⟫_ℝ=⟪v,operator μ c hc U hb w⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae μ c hc U hb v,operator_ae μ c hc U hb w] with x hv hw
  rw [hv,hw]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

theorem operator_commute (c d : X → ℝ) (hc : AEStronglyMeasurable c μ)
    (hd : AEStronglyMeasurable d μ) (U V : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (he : ∀ᵐ x ∂μ,‖d x‖ ≤ V) (v : Lp ℝ 2 μ) :
    operator μ c hc U hb (operator μ d hd V he v)=
      operator μ d hd V he (operator μ c hc U hb v) := by
  apply Lp.ext
  filter_upwards [operator_ae μ c hc U hb (operator μ d hd V he v),
    operator_ae μ d hd V he (operator μ c hc U hb v),
    operator_ae μ c hc U hb v,operator_ae μ d hd V he v] with x hcd hdc hc hd
  rw [hcd,hdc,hc,hd]
  ring

theorem operator_sum_squares (c d : X → ℝ) (hc : AEStronglyMeasurable c μ)
    (hd : AEStronglyMeasurable d μ) (U V : ℝ)
    (hb : ∀ᵐ x ∂μ,‖c x‖ ≤ U) (he : ∀ᵐ x ∂μ,‖d x‖ ≤ V)
    (hunit : ∀ᵐ x ∂μ,(c x)^2+(d x)^2=1) (v : Lp ℝ 2 μ) :
    operator μ c hc U hb (operator μ c hc U hb v)+
      operator μ d hd V he (operator μ d hd V he v)=v := by
  apply Lp.ext
  filter_upwards [operator_ae μ c hc U hb (operator μ c hc U hb v),
    operator_ae μ d hd V he (operator μ d hd V he v),
    operator_ae μ c hc U hb v,operator_ae μ d hd V he v,
    Lp.coeFn_add (operator μ c hc U hb (operator μ c hc U hb v))
      (operator μ d hd V he (operator μ d hd V he v)),hunit] with x hcc hdd hc hd hadd hu
  rw [hadd]
  simp only [Pi.add_apply,hcc,hdd,hc,hd]
  calc
    _ = ((c x)^2+(d x)^2)*v x := by ring
    _ = v x := by rw [hu,one_mul]

end SHE.RealMultiplier
