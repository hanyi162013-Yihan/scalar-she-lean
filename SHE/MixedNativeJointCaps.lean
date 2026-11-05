module

public import SHE.NativeObservationCaps
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointCaps
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeJointCaps_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeJointCaps_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeJointCaps_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeJointCaps_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeJointCaps_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeJointCaps_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)


/-- Actual prefix rows are clipped before applying the generic finite
Ito formula. This changes no observation on the covered prefix. -/
def clippedRows (c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target) (hΛ : 0≤Λ) (i : Fin n) :
    Process (E:=Both RealHaarInput) 𝓕 μ H :=
  StoppedItoInputs.stop 𝓕 μ H (c:ℝ)
    (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap hΛ i)

theorem clippedRows_bound (hΛ : 0≤Λ) (c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)
    (hstop : ∀ i,(c:ℝ)≤(Z i).stop) (i : Fin n) :
    ∀ᵐ p ∂energyMeasure μ H,‖clippedRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap hΛ i p‖^2≤
      NativeObservationCaps.cap (κ+10*M) ((Z i).target-(c:ℝ)) := by
  have hm : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hC := NativeObservationCaps.cap_nonneg (show 0≤κ+10*M by positivity) (sub_pos.mpr (hgap i))
  filter_upwards [StoppedItoInputs.stop_ae 𝓕 μ H (c:ℝ)
    (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap hΛ i),
    MixedNativeJointPhysicalRows.rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap]
    with p hp hrow
  change ‖StoppedItoInputs.stop 𝓕 μ H (c:ℝ) _ p‖^2≤_
  rw [hp]
  by_cases hpc : p∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ)
  · rw [Set.indicator_of_mem hpc,hrow (by exact_mod_cast hpc) i]
    have hpr : (p.1:ℝ)≤(c:ℝ) := le_of_lt hpc
    have h0 := NativeObservationProcess.row_norm_sq_bound hκ (AdditiveHaarForcing.constantField κ hκ)
      (hgap i) hpr (Z i).center
    have hu := NativeObservationProcess.row_norm_sq_bound hell
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first p) (hgap i) hpr (Z i).center
    have hv := NativeObservationProcess.row_norm_sq_bound hell
      (ContinuousHeatMild.coefficientFunction haV hell hbV S.second p) (hgap i) hpr (Z i).center
    have he0 : 0≤Real.exp (-Λ*((Z i).stop-(p.1:ℝ))) := (Real.exp_pos _).le
    have he1 : Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr (hpr.trans (hstop i))))
    have hr : |1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hk := NativeObservationCaps.cap_nonneg hm (sub_pos.mpr (hgap i))
    have hres := NativeObservationCaps.residual_bound
      (MixedNativeJointPhysicalRows.firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
      (MixedNativeJointPhysicalRows.secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)
      hr hk hu hv
    rw [MixedNativeJointPhysicalRows.physicalRow,WithLp.prod_norm_sq_eq_of_L2]
    change ‖MixedNativeJointPhysicalRows.additiveRow κ hκ Z p i‖^2+
      ‖MixedNativeJointPhysicalRows.secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i+
        (1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) •
        (MixedNativeJointPhysicalRows.firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i-
          MixedNativeJointPhysicalRows.secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z p i)‖^2≤_
    exact (add_le_add h0 hres).trans_eq (by unfold NativeObservationCaps.cap; ring)
  · rw [Set.indicator_of_notMem hpc,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact hC

end SHE.MixedNativeJointCaps
