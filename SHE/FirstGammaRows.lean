module

public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
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

namespace SHE.FirstGammaRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaRows_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)


open MixedNativePairScaledMartingale

/-- Original extended martingale: ordinary heat U and exponentially
rescaled D=V-U, with their full common two-channel noise. -/
def actual : Fin (n+n)→Process (E:=Both RealHaarInput) 𝓕 μ H :=
  MixedNativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (fun i=>(Z i).target) (fun i=>(Z i).center) c hgap hΛ

/-- Only the ordinary U block is replaced after v. The old D block is
frozen, making the initial controlled difference a finite coordinate. -/
def replacement (θ : ℝ) : Fin (n+n)→Process (E:=Both RealHaarInput) 𝓕 μ H :=
  Fin.append
    (PastFrozenPrefixRows.rows 𝓕 μ H P Λ κ θ hκ hκP v
      (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
      (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) Z c hgap)
    (fun _=>0)

def cap : Fin (n+n)→ℝ := Fin.append
  (fun i=>NativeObservationCaps.cap (κ+M) ((Z i).target-(c:ℝ)))
  (fun i=>Real.exp (Λ*(c:ℝ))^2*(4*NativeObservationCaps.cap M ((Z i).target-(c:ℝ))))

include hell hbU hκ hgap in
theorem cap_nonneg (i : Fin (n+n)) : 0≤cap (M:=M) Λ κ Z c i := by
  have hM : 0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [cap,Fin.append_left]
    exact NativeObservationCaps.cap_nonneg (add_nonneg hκ.le hM) (sub_pos.mpr (hgap j))
  · simp only [cap,Fin.append_right]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (NativeObservationCaps.cap_nonneg hM (sub_pos.mpr (hgap j))))

/-- Every extended row has an actual pathwise finite prefix cap. The
exponential cap is used only for ordinary Itô applicability. -/
theorem actual_bound (i : Fin (n+n)) : ∀ᵐ p∂energyMeasure μ H,
    ‖actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap i p‖^2≤cap (M:=M) Λ κ Z c i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [actual,MixedNativePairExtendedMartingale.rows,Fin.append_left,cap,
      MixedNativeFrozenInterpolationRows.ordinaryRows] using
      MixedNativeFrozenInterpolationRows.ordinaryRows_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap j
  · simp only [actual,MixedNativePairExtendedMartingale.rows,Fin.append_right,cap]
    have hm : 0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
    let U:=NativeObservationProcess.process 𝓕 μ H hell hm
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (hgap j) (Z j).center
    let V:=NativeObservationProcess.process 𝓕 μ H hell hm
      (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (hgap j) (Z j).center
    let N:=normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ c (hgap j) (Z j).center
    let R:=MixedNativePairLocalMartingale.row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ c (hgap j) (Z j).center
    have hU:=NativeObservationCaps.process_bound 𝓕 μ H hell hm
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (hgap j) (Z j).center
    have hV:=NativeObservationCaps.process_bound 𝓕 μ H hell hm
      (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (hgap j) (Z j).center
    have hw:=PredictableContraction.weighted_ae 𝓕 μ H (PredictableDamping.weight Λ c)
      (PredictableDamping.weight_predictable 𝓕 Λ c) (PredictableDamping.weight_bound hΛ c) (V-U)
    have hr:=PredictableItoRotation.processIsometry_ae 𝓕 μ H
      (fun _=>right (C:=RealHaarInput)) (right_measurable 𝓕) R
    filter_upwards [hU,hV,hw,hr,ae_eq_of_ae_eq_trim (Lp.coeFn_sub V U),
      ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.exp (Λ*(c:ℝ))) N)] with p hu hv hw hr hs he
    change ‖NativeHybridInput.rightLift 𝓕 μ H R p‖^2≤_
    rw [NativeHybridInput.rightLift,hr,(right (C:=RealHaarInput)).norm_map]
    change ‖(Real.exp (Λ*(c:ℝ)) • N) p‖^2≤_
    rw [he]
    simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
    change Real.exp (Λ*(c:ℝ))^2*‖N p‖^2≤Real.exp (Λ*(c:ℝ))^2*(4*NativeObservationCaps.cap M ((Z j).target-(c:ℝ)))
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    change N p=PredictableDamping.weight Λ c p • (V-U) p at hw
    rw [hw,hs]
    simp only [Pi.sub_apply]
    have hn : ‖PredictableDamping.weight Λ c p • (V p-U p)‖≤‖V p-U p‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (PredictableDamping.weight_bound hΛ c p) (norm_nonneg _)).trans_eq (one_mul _)
    have hd := (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (V p) (U p)) 2).trans
      (add_pow_le (norm_nonneg _) (norm_nonneg _) 2)
    have hn2:=pow_le_pow_left₀ (norm_nonneg _) hn 2
    norm_num only at hd
    linarith

end SHE.FirstGammaRows
