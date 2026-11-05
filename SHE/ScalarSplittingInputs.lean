module
public import SHE.NoiseSplitting
public import SHE.PairedHilbertIsometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.ScalarSplittingInputs
open MeasureTheory NoiseSplitting
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) (g : X → ℝ) (hg : AEStronglyMeasurable g ν)
variable (m C : ℝ) (hm : 0 < m)
variable (hgap : ∀ᵐx∂ν, m ≤ |g x|) (hbound : ∀ᵐx∂ν, |g x| ≤ C)

include hg in
theorem root_measurable : AEStronglyMeasurable (fun x => Real.sqrt ((g x)^2-m^2)) ν :=
  Real.continuous_sqrt.comp_aestronglyMeasurable ((hg.pow 2).sub aestronglyMeasurable_const)

include hbound in
theorem root_bound : ∀ᵐx∂ν, ‖Real.sqrt ((g x)^2-m^2)‖ ≤ |C| := by
  filter_upwards [hbound] with x hx
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_left (abs_nonneg C)).mpr
  nlinarith [sq_abs (g x),sq_abs C,sq_nonneg m,abs_nonneg (g x)]

def residualInput (v : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  RealMultiplier.operator ν (fun x => Real.sqrt ((g x)^2-m^2))
    (root_measurable ν g hg m) |C| (root_bound ν g m C hbound) v

def originalInput (v : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  RealMultiplier.operator ν g hg |C|
    (hbound.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self C))) v

include hm hgap hbound in
/-- The literal physical splitting maps additive plus residual input
back to the original g-input and zero auxiliary input. It is valid for
either sign of g and uses the SAME predictable orthogonal rotation. -/
theorem reconstruct (v : Lp ℝ 2 ν) :
    physicalRotation ν g hg m hm hgap
      (WithLp.toLp 2 (m • v,residualInput ν g hg m C hbound v)) =
    WithLp.toLp 2 (originalInput ν g hg C hbound v,0) := by
  have hrot := physicalRotation_ae ν g hg m hm hgap
    (WithLp.toLp 2 (m • v,residualInput ν g hg m C hbound v))
  have hroot := RealMultiplier.operator_ae ν (fun x => Real.sqrt ((g x)^2-m^2))
    (root_measurable ν g hg m) |C| (root_bound ν g m C hbound) v
  have horig := RealMultiplier.operator_ae ν g hg |C|
    (hbound.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self C))) v
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hrot,hroot,horig,Lp.coeFn_smul m v,hgap] with x hr hs ho hmval hx
    change (physicalRotation ν g hg m hm hgap
      (WithLp.toLp 2 (m • v,residualInput ν g hg m C hbound v))).fst x =
      originalInput ν g hg C hbound v x
    rw [hr.1]
    change additiveRatio m (g x)*(m • v) x + residualRatio m (g x)*(residualInput ν g hg m C hbound v) x = originalInput ν g hg C hbound v x
    change residualInput ν g hg m C hbound v x = _ at hs
    change originalInput ν g hg C hbound v x = _ at ho
    rw [hmval,hs,ho]
    have he := (splitting_scalar hm hx).2.2.2.1
    change additiveRatio m (g x)*(m*v x)+residualRatio m (g x)*(Real.sqrt ((g x)^2-m^2)*v x)=g x*v x
    calc
      _ = (m*additiveRatio m (g x)+Real.sqrt ((g x)^2-m^2)*residualRatio m (g x))*v x := by ring
      _ = _ := by rw [he]
  · apply Lp.ext
    filter_upwards [hrot,hroot,Lp.coeFn_smul m v,hgap,
      Lp.coeFn_zero (E:=ℝ) (p:=2) ν] with x hr hs hmval hx hz
    change (physicalRotation ν g hg m hm hgap
      (WithLp.toLp 2 (m • v,residualInput ν g hg m C hbound v))).snd x =
      (0 : Lp ℝ 2 ν) x
    rw [hr.2]
    change residualRatio m (g x)*(m • v) x - additiveRatio m (g x)*(residualInput ν g hg m C hbound v) x = (0 : Lp ℝ 2 ν) x
    change residualInput ν g hg m C hbound v x = _ at hs
    rw [hmval,hs,hz]
    have he := (splitting_scalar hm hx).2.2.2.2
    change residualRatio m (g x)*(m*v x)-additiveRatio m (g x)*(Real.sqrt ((g x)^2-m^2)*v x)=0
    calc
      _ = (m*residualRatio m (g x)-Real.sqrt ((g x)^2-m^2)*additiveRatio m (g x))*v x := by ring
      _ = _ := by rw [he,zero_mul]
end SHE.ScalarSplittingInputs
