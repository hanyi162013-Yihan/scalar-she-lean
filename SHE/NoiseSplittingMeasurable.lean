module

public import SHE.NoiseSplitting
public import SHE.MeasurableL2Field
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.RealMultiplier
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
variable (μ : Measure X)

theorem realL2_norm_sq (v : Lp ℝ 2 μ) : ‖v‖^2=∫ x,‖v x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

variable [SFinite μ] [SecondCountableTopology (Lp ℝ 2 μ)]
variable [MeasurableSpace (Lp ℝ 2 μ)] [BorelSpace (Lp ℝ 2 μ)]

theorem operator_measurable_fixed (F : P × X → ℝ) (hF : Measurable F) (U : ℝ)
    (hbound : ∀ p,∀ᵐ x ∂μ,‖F (p,x)‖ ≤ U) (v : Lp ℝ 2 μ) :
    Measurable (fun p => operator μ (fun x => F (p,x))
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable U (hbound p) v) := by
  apply MeasurableL2Field.measurable_of_dist
  intro w
  have hm : Measurable (fun p : P × X => ‖F p*v p.2-w p.2‖^2) :=
    ((hF.mul ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)).sub
      ((Lp.stronglyMeasurable w).measurable.comp measurable_snd)).norm.pow_const 2
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.sqrt
  convert hi using 1
  funext p
  rw [dist_eq_norm]
  have he : ‖operator μ (fun x => F (p,x))
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable U (hbound p) v-w‖^2=
      ∫ x,‖F (p,x)*v x-w x‖^2 ∂μ := by
    rw [realL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [operator_ae μ (fun x => F (p,x))
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable U (hbound p) v,
      Lp.coeFn_sub (operator μ (fun x => F (p,x))
        (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable U (hbound p) v) w] with x hm hs
    rw [hs,Pi.sub_apply,hm]
  rw [← he,Real.sqrt_sq (norm_nonneg _)]

/-- A jointly measurable bounded physical multiplier acts measurably on
arbitrary measurable real L² inputs. The parameter sigma algebra may be
the predictable sigma algebra. -/
theorem operator_measurable_process (F : P × X → ℝ) (hF : Measurable F) (U : ℝ)
    (hbound : ∀ p,∀ᵐ x ∂μ,‖F (p,x)‖ ≤ U) (v : P → Lp ℝ 2 μ) (hv : Measurable v) :
    Measurable (fun p => operator μ (fun x => F (p,x))
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable U (hbound p) (v p)) := by
  let A (z : Lp ℝ 2 μ) (p : P) := operator μ (fun x => F (p,x))
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable U (hbound p) z
  have hm : Measurable (Function.uncurry A) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun p => (operator μ (fun x => F (p,x)) _ U (hbound p)).continuous)
      (operator_measurable_fixed μ F hF U hbound)
  exact hm.comp (hv.prodMk measurable_id)

end SHE.RealMultiplier

namespace SHE.NoiseSplitting
open MeasureTheory
open scoped ENNReal
variable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
variable (μ : Measure X) [SFinite μ] [SecondCountableTopology (Lp ℝ 2 μ)]
variable [MeasurableSpace (Lp ℝ 2 μ)] [BorelSpace (Lp ℝ 2 μ)]

theorem physicalRotation_measurable_pair (F : P × X → ℝ) (hF : Measurable F)
    (m : ℝ) (hm : 0 < m) (hgap : ∀ p,∀ᵐ x ∂μ,m ≤ |F (p,x)|)
    (v w : P → Lp ℝ 2 μ) (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun p => physicalRotation μ (fun x => F (p,x))
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable m hm (hgap p)
      (WithLp.toLp 2 (v p,w p))) := by
  have hA : Measurable (fun p => additiveRatio m (F p)) := measurable_const.div hF
  have hB : Measurable (fun p => residualRatio m (F p)) :=
    ((hF.pow_const 2).sub measurable_const).sqrt.div hF
  have bA : ∀ p,∀ᵐ x ∂μ,‖additiveRatio m (F (p,x))‖ ≤ 1 :=
    fun p => additiveRatio_bound μ _ m hm (hgap p)
  have bB : ∀ p,∀ᵐ x ∂μ,‖residualRatio m (F (p,x))‖ ≤ 1 :=
    fun p => residualRatio_bound μ _ m hm (hgap p)
  have hAv := RealMultiplier.operator_measurable_process μ _ hA 1 bA v hv
  have hAw := RealMultiplier.operator_measurable_process μ _ hA 1 bA w hw
  have hBv := RealMultiplier.operator_measurable_process μ _ hB 1 bB v hv
  have hBw := RealMultiplier.operator_measurable_process μ _ hB 1 bB w hw
  exact (WithLp.measurable_toLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ)).comp
    ((hAv.add hBw).prodMk (hBv.sub hAw))

/-- Substitution of any jointly measurable physical coefficient field
into the exact orthogonal splitting preserves the parameter sigma algebra,
including a supplied predictable sigma algebra. -/
theorem physicalRotation_measurable_process (F : P × X → ℝ) (hF : Measurable F)
    (m : ℝ) (hm : 0 < m) (hgap : ∀ p,∀ᵐ x ∂μ,m ≤ |F (p,x)|)
    (v : P → WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ)) (hv : Measurable v) :
    Measurable (fun p => physicalRotation μ (fun x => F (p,x))
      (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable m hm (hgap p) (v p)) := by
  have hp := (WithLp.measurable_ofLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ)).comp hv
  exact physicalRotation_measurable_pair μ F hF m hm hgap (fun p => (v p).fst) (fun p => (v p).snd)
    (measurable_fst.comp hp) (measurable_snd.comp hp)

end SHE.NoiseSplitting
