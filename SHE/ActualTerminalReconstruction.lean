module
public import SHE.MixedNativeLowBandEnergy
public import SHE.SmoothHeatBandReconstruction
public import SHE.ActualTerminalBandField

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.ActualTerminalReconstruction
open MeasureTheory AddCircle GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaReferenceEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable (D:SmoothApproximation.ScalarData)(n:ℕ)
local notation "ha"=>D.smooth_boundedSmooth n
local notation "hB"=>ScalarApproximationDiscrepancy.smooth_abs_bound D n
local notation "hU"=>(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
local notation "hV"=>(S.second_predictable.mono (predictable_le_product 𝓕)).measurable
variable (hL:1≤Λ){ρ:ℝ}(hρ:0<ρ)
def terminal(j:ℕ)(z:ℝ≥0×Ω):CircleL2:=ActualTerminalBandField.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S (a:=D.smoothCoefficient n) j hL hρ z
local notation "Terminal"=>terminal 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ
local notation "Low"=>MixedNativeLowBandEnergy.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ.le
def full(z:ℝ≥0×Ω):CircleL2:=SmoothHeatBandReconstruction.difference ha Λ ρ hL hρ.le
  (S.first z.1 z.2) (S.second z.1 z.2)
local notation "Full"=>full 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ

theorem terminal_eq(j:ℕ)(z:ℝ≥0×Ω):Terminal j z=
    SmoothHeatBandReconstruction.high ha Λ ρ hL hρ.le j (S.first z.1 z.2) (S.second z.1 z.2):=
  SmoothScalarField.bessel_native Λ ρ hL hρ.le (ScalarHeatBands.band_boundedSmooth ha (j+1))
    (Function.uncurry S.first) (Function.uncurry S.second) hU hV z

theorem low_eq(J:ℕ)(z:ℝ≥0×Ω):Low J z=
    SmoothHeatBandReconstruction.low ha Λ ρ hL hρ.le J (S.first z.1 z.2) (S.second z.1 z.2):=by
  change OneInputOperator.besselHalf Λ ρ hL hρ.le (CircleNormalization.push _) =
    OneInputOperator.besselHalf Λ ρ hL hρ.le (CircleNormalization.push _)
  congr 1
  congr 1
  apply Lp.ext
  filter_upwards [MixedNativeLowBandEnergy.unit_ae
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n J z,
    SmoothScalarField.ae (ScalarHeatBands.smooth_boundedSmooth ha J) (S.second z.1 z.2),
    SmoothScalarField.ae (ScalarHeatBands.smooth_boundedSmooth ha J) (S.first z.1 z.2),
    Lp.coeFn_sub (SmoothHeatBandReconstruction.smooth ha J (S.second z.1 z.2))
      (SmoothHeatBandReconstruction.smooth ha J (S.first z.1 z.2))] with x hl hv hu hs
  simp only [SmoothHeatBandReconstruction.smooth] at hs ⊢
  rw [hl,hs,Pi.sub_apply,hv,hu]

/-- Exact terminal slots reconstruct the true smooth-root difference
up to a uniform upper-frequency tail. This bound is fixed before n. -/
theorem finite_reconstruction(J m:ℕ)(z:ℝ≥0×Ω):
    ‖Full z-Low J z-(∑r∈Finset.range m,Terminal (J+r) z)‖≤
      2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)*CompactMollifier.radius (J+m)^D.beta:=by
  have ht:(∑r∈Finset.range m,Terminal (J+r) z)=
      ∑r∈Finset.range m,SmoothHeatBandReconstruction.high ha Λ ρ hL hρ.le (J+r)
        (S.first z.1 z.2) (S.second z.1 z.2):=by
    apply Finset.sum_congr rfl
    intro r _
    exact terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ (J+r) z
  rw [ht,low_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J z]
  exact SmoothHeatBandReconstruction.reconstruction ha hB D.holderConstant_nonneg
    D.beta_pos.le (D.smooth_holder n) Λ ρ hL hρ.le J m (S.first z.1 z.2) (S.second z.1 z.2)

/-- The actual mixed coefficient input has only ONE original-U side
approximation error. It is not silently replaced by a smooth-smooth input. -/
def mixed(z:ℝ≥0×Ω):CircleL2:=OneInputOperator.besselHalf Λ ρ hL hρ.le (CircleNormalization.push
  (ScalarApproximationDiscrepancy.smoothField D n (S.second z.1 z.2)-
    ScalarApproximationDiscrepancy.roughField D (S.first z.1 z.2)))
local notation "Mixed"=>mixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ

theorem mixed_error(z:ℝ≥0×Ω):‖Mixed z-Full z‖≤ScalarApproximationDiscrepancy.scalarError D n:=by
  have hval(U:RealL2):SmoothScalarField.value ha U=ScalarApproximationDiscrepancy.smoothField D n U:=
    SmoothScalarField.eq_coefficient ha (D.smooth_boundedSmooth n).smooth.continuous.measurable D.cap hB U
  have he:Mixed z-Full z=OneInputOperator.besselHalf Λ ρ hL hρ.le (CircleNormalization.push
      (ScalarApproximationDiscrepancy.smoothField D n (S.first z.1 z.2)-
        ScalarApproximationDiscrepancy.roughField D (S.first z.1 z.2))):=by
    simp only [mixed,full,SmoothHeatBandReconstruction.difference,hval,map_sub]
    abel
  rw [he]
  calc
    _≤‖CircleNormalization.push (ScalarApproximationDiscrepancy.smoothField D n (S.first z.1 z.2)-
        ScalarApproximationDiscrepancy.roughField D (S.first z.1 z.2))‖:=
      OneInputOperator.besselHalf_norm_le Λ ρ hL hρ.le _
    _=‖ScalarApproximationDiscrepancy.smoothField D n (S.first z.1 z.2)-
        ScalarApproximationDiscrepancy.roughField D (S.first z.1 z.2)‖:=CircleNormalization.push.norm_map _
    _≤_:=by
      rw [norm_sub_rev]
      exact ScalarApproximationDiscrepancy.field_error D n (S.first z.1 z.2)

/-- Full mixed-input finite reconstruction with both honest errors:
scalar smoothing on the U side and a uniform terminal heat-cutoff tail. -/
theorem mixed_reconstruction(J m:ℕ)(z:ℝ≥0×Ω):
    ‖Mixed z-Low J z-(∑r∈Finset.range m,Terminal (J+r) z)‖≤
      ScalarApproximationDiscrepancy.scalarError D n+
      2*(D.holderConstant*GaussianAudit.gaussianAbsMoment D.beta)*CompactMollifier.radius (J+m)^D.beta:=by
  have he:Mixed z-Low J z-(∑r∈Finset.range m,Terminal (J+r) z)=
      (Mixed z-Full z)+(Full z-Low J z-(∑r∈Finset.range m,Terminal (J+r) z)):=by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (mixed_error
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ z)
    (finite_reconstruction 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S D n hL hρ J m z))

end SHE.ActualTerminalReconstruction
