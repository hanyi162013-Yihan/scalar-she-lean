module

public import SHE.MixedNativeJointCaps

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MixedNativePhysicalRowBound
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)


/-- A pointwise bound for the literal physical row on every positive-gap
prefix. This avoids parameter-dependent exceptional events when
integrating the original history. -/
theorem row_bound (hΛ:0≤Λ)(c:ℝ≥0)(hgap:∀i,(c:ℝ)<(Z i).target)
    (hstop:∀i,(c:ℝ)≤(Z i).stop)(p:ℝ≥0×Ω)(hpc:(p.1:ℝ)≤(c:ℝ))(i:Fin n):
    ‖MixedNativeJointPhysicalRows.physicalRow
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i‖^2≤
        NativeObservationCaps.cap (κ+10*M) ((Z i).target-(c:ℝ)):=by
  have hm:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have h0:=NativeObservationProcess.row_norm_sq_bound hκ (AdditiveHaarForcing.constantField κ hκ)
    (hgap i) hpc (Z i).center
  have hu:=NativeObservationProcess.row_norm_sq_bound hell
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first p) (hgap i) hpc (Z i).center
  have hv:=NativeObservationProcess.row_norm_sq_bound hell
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second p) (hgap i) hpc (Z i).center
  have he0:0≤Real.exp (-Λ*((Z i).stop-(p.1:ℝ))):=(Real.exp_pos _).le
  have he1:Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))≤1:=Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr (hpc.trans (hstop i))))
  have hr:|1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))|≤1:=abs_le.mpr ⟨by linarith,by linarith⟩
  have hk:=NativeObservationCaps.cap_nonneg hm (sub_pos.mpr (hgap i))
  have hres:=NativeObservationCaps.residual_bound
    (MixedNativeJointPhysicalRows.firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
    (MixedNativeJointPhysicalRows.secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
    hr hk hu hv
  rw [MixedNativeJointPhysicalRows.physicalRow,WithLp.prod_norm_sq_eq_of_L2]
  exact (add_le_add h0 hres).trans_eq (by unfold NativeObservationCaps.cap;ring)

/-- The same single finite cap works for all observation geometries
with a prescribed positive heat gap. -/
theorem row_bound_uniform (hΛ:0≤Λ)(c:ℝ≥0){ε:ℝ}(hε:0<ε)
    (hgap:∀i,ε≤(Z i).target-(c:ℝ))(hstop:∀i,(c:ℝ)≤(Z i).stop)
    (p:ℝ≥0×Ω)(hpc:(p.1:ℝ)≤(c:ℝ))(i:Fin n):
    ‖MixedNativeJointPhysicalRows.physicalRow
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i‖^2≤
        NativeObservationCaps.cap (κ+10*M) ε:=by
  have hg:∀i,(c:ℝ)<(Z i).target:=fun i=>by linarith [hgap i]
  refine (row_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hg hstop p hpc i).trans ?_
  unfold NativeObservationCaps.cap
  apply mul_le_mul_of_nonneg_left _ (by
    have hm:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
    positivity)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hε (hgap i) (by norm_num)) StoppedFourier.heatConstant_pos.le)

end SHE.MixedNativePhysicalRowBound
