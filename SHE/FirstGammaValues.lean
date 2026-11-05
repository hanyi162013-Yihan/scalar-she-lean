module

public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FiniteReferenceSpliceRows
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
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaValues
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open FirstGammaConstruction
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hH hH0 B hBDG hIJ₀ hIJ₁ in
theorem left_eq_original (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hqc : q≤c) :
    (fun ω=>FiniteComparisonTest.left (n+n) (Y θ (q,ω)))=ᵐ[μ]
      MixedNativePairExtendedMartingale.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (fun i=>(Z i).target) (fun i=>(Z i).center) c q := by
  filter_upwards [FirstGammaConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap hH hH0 B hBDG θ q (hqc.trans hcH),
    MixedNativePairExtendedMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ (fun i=>(Z i).target) (fun i=>(Z i).center) c hgap hΛ hcH q]
    with ω hj ho
  rw [hj,ho]
  apply PiLp.ext
  intro i
  simp only [FiniteComparisonTest.left_apply,StandardFiniteIto.vectorIntegral,FiniteReferenceSplice.jointInitial,
    FiniteReferenceSplice.jointRows,WithLp.ofLp_toLp,Fin.append_left,FirstGammaRows.actual]

include hH hH0 B hBDG hIJ₀ hIJ₁ in
theorem currentU_eq (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hqc : q≤c) :
    ∀ᵐ ω∂μ,∀ i,FirstGammaAffine.currentU n (Y θ (q,ω)) i=
      functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω) := by
  filter_upwards [left_eq_original 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hqc] with ω hω i
  change ObservationBlockMaps.first n (FiniteComparisonTest.left (n+n) (Y θ (q,ω))) i=_
  rw [hω]
  simp only [ObservationBlockMaps.first_apply,MixedNativePairExtendedMartingale.value,WithLp.ofLp_toLp,Fin.append_left]
  change PositiveGapObservations.coordinate ((Z i).target-(c:ℝ)) (Z i).target (Z i).center
    (Function.uncurry S.first) (min q c,ω)=_
  rw [min_eq_left hqc,PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
    (sub_le_sub_left (by exact_mod_cast hqc) _)]
  rfl

include hH hH0 B hBDG hIJ₀ hIJ₁ in
theorem currentD_eq (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hqc : q≤c) :
    ∀ᵐ ω∂μ,∀ i,FirstGammaAffine.currentD n (Y θ (q,ω)) i=
      Real.exp (Λ*(q:ℝ))*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω) := by
  filter_upwards [left_eq_original 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hqc] with ω hω i
  change ObservationBlockMaps.second n (FiniteComparisonTest.left (n+n) (Y θ (q,ω))) i=_
  rw [hω]
  simp only [ObservationBlockMaps.second_apply,MixedNativePairExtendedMartingale.value,WithLp.ofLp_toLp,Fin.append_right]
  change MixedNativePairLocalMartingale.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S c
    (Z i).target (Z i).center q ω=_
  unfold MixedNativePairLocalMartingale.value
  rw [min_eq_left hqc,PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
      (sub_le_sub_left (by exact_mod_cast hqc) _),
    PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
      (sub_le_sub_left (by exact_mod_cast hqc) _),map_sub]
  rfl

end SHE.FirstGammaValues
