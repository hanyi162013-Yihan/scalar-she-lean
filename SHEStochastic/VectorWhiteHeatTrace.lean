module

public import SHEStochastic.VectorWhiteCoordinates
public import SHEStochastic.VectorHilbertColumns
public import SHE.NativeHeatObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.VectorWhiteHeatTrace
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation VectorWhiteCoordinates
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem embed_single (q : HaarNode) :
    realInputEmbed (lp.single 2 q (1 : ℝ) : RealHaarInput) = (lp.single 2 q (1 : ℂ) : HaarInput) := by
  apply lp.ext
  funext r
  by_cases h : q = r
  · subst r
    simp [realInputEmbed, lp.single_apply]
  · simp [realInputEmbed, lp.single_apply, Pi.single_eq_of_ne (Ne.symm h)]

theorem scalar_column {t : ℝ} (ht : 0 < t) (q : HaarNode) :
    RealHeat.realHeat t (AdditivePhysicalFactor.whiteCoordinates 1 zero_lt_one (lp.single 2 q 1)) =
      RealHaarIntegrand.kernel 1 1 zero_lt_one (t, AdditiveHaarForcing.constantField 1 zero_lt_one) q := by
  have hf := AdditivePhysicalFactor.factor_constant 1 zero_lt_one (lp.single 2 q (1 : ℝ))
  rw [embed_single, fieldFactor, factor_single] at hf
  simp only [Real.sqrt_one, one_smul] at hf
  rw [← hf]
  change realPart (CircleHeat.heat t (realEmbed (realPart
    (globalHaarColumn q (AdditiveHaarForcing.constantField 1 zero_lt_one).val)))) = _
  rw [NativeHeatObservation.realEmbed_realPart_of_real _
    (globalHaarColumn_real_ae q _ (AdditiveHaarForcing.constantField 1 zero_lt_one).property.1)]
  change _ = realPart (HaarHeatIntegrand.kernel 1 1 zero_lt_one
    (t, AdditiveHaarForcing.constantField 1 zero_lt_one) q)
  rw [HaarHeatIntegrand.kernel_apply, if_pos ht]

theorem basis_lift (i : d) (q : HaarNode) :
    basis (i, q) = VectorHilbertColumns.lift i
      (AdditivePhysicalFactor.whiteCoordinates 1 zero_lt_one (lp.single 2 q 1)) := by
  apply analysis.injective
  rw [← synthesis_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext k
  rcases k with ⟨j, r⟩
  rw [coordinate]
  change (lp.single 2 (i, q) (1 : ℝ) : Input (d := d)) (j, r) =
    scalar (VectorHeat.coordinates (VectorHilbertColumns.lift i
      (AdditivePhysicalFactor.whiteCoordinates 1 zero_lt_one (lp.single 2 q 1))) j) r
  unfold VectorHilbertColumns.lift
  rw [LinearIsometryEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst j
    simp [PiLp.single_apply, scalar, lp.single_apply, Pi.single_apply, Prod.mk.injEq]
  · simp [PiLp.single_apply, h, scalar, lp.single_apply, Prod.mk.injEq]

theorem trace {t : ℝ} (ht : 0 < t) :
    Summable (fun k : d × HaarNode => ‖VectorHeat.heat t (basis k)‖ ^ 2) ∧
      (∑' k : d × HaarNode, ‖VectorHeat.heat t (basis k)‖ ^ 2) ≤
        (Fintype.card d : ℝ) * (1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * t ^ (-(1/2 : ℝ))) := by
  let K := RealHaarIntegrand.kernel 1 1 zero_lt_one (t, AdditiveHaarForcing.constantField 1 zero_lt_one)
  have he (k : d × HaarNode) : ‖VectorHeat.heat t (basis k)‖ ^ 2 =
      ‖VectorHilbertColumns.columns (d := d) K k‖ ^ 2 := by
    rw [basis_lift, VectorHilbertColumns.heat_lift, scalar_column ht]
    rfl
  have hs : Summable (fun k : d × HaarNode => ‖VectorHilbertColumns.columns (d := d) K k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (VectorHilbertColumns.columns (d := d) K)).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  refine ⟨by simpa only [he] using hs, ?_⟩
  simp only [he]
  rw [← HilbertColumns.norm_sq, VectorHilbertColumns.norm_sq, RealHaarIntegrand.kernel_norm_sq]
  have hh := HaarHeatIntegrand.kernel_norm_sq_bound zero_lt_one ht (AdditiveHaarForcing.constantField 1 zero_lt_one)
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (Fintype.card d))

end SHEStochastic.VectorWhiteHeatTrace
