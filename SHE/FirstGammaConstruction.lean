module

public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
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

namespace SHE.FirstGammaConstruction
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaConstruction_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaConstruction_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaConstruction_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaConstruction_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaConstruction_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaConstruction_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaConstruction_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaConstruction_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open FirstGammaRows
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)

def replacementCap : Fin (n+n)→ℝ := Fin.append
  (fun i=>NativeObservationCaps.cap P.upper ((Z i).target-(c:ℝ))) (fun _=>0)

include hgap in
theorem replacementCap_nonneg (i : Fin (n+n)) : 0≤replacementCap Z P c i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [replacementCap,Fin.append_left] using
      NativeObservationCaps.cap_nonneg P.upper_nonneg (sub_pos.mpr (hgap j))
  · simp only [replacementCap,Fin.append_right,le_refl]

theorem replacement_bound (θ : ℝ) (i : Fin (n+n)) : ∀ᵐ p∂energyMeasure μ H,
    ‖Rnew θ i p‖^2≤replacementCap Z P c i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simpa only [FirstGammaRows.replacement,Fin.append_left,replacementCap] using
      PastFrozenPrefixRows.rows_bound 𝓕 μ H P Λ κ θ hκ hκP v
        (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
        (MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
        Z c hgap j
  · filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_zero (E:=Both RealHaarInput)
      (μ:=(energyMeasure μ H).trim (predictable_le_product 𝓕)) (p:=2))] with p hp
    simp only [FirstGammaRows.replacement,replacementCap,Fin.append_right,hp,Pi.zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),le_refl]

def value (θ : ℝ) : ℝ≥0×Ω→FirstGammaAffine.Space n :=
  FiniteReferenceSplice.value 𝓕 μ H v Rold (Rnew θ) J z₀

theorem continuous_value (θ : ℝ) (hH0 : 0<H) (ω : Ω) :
    Continuous (fun t=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap θ (t,ω)) :=
  BoundedVectorIntegral.continuous_value 𝓕 μ H J (FiniteReferenceSplice.jointInitial z₀) _ hH0 ω

variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)

include hH hH0 B hBDG in
theorem predictable_value (θ : ℝ) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ) :
    StronglyMeasurable[𝓕.predictable]
      (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap θ) :=
  FiniteReferenceSplice.predictable_value 𝓕 μ H v Rold (Rnew θ) J z₀
    (FirstGammaRows.cap (M:=M) Λ κ Z c) (replacementCap Z P c)
    (FirstGammaRows.cap_nonneg Λ κ hκ hell hbU Z c hgap) (replacementCap_nonneg Z P c hgap)
    (FirstGammaRows.actual_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap)
    (replacement_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap θ)
    hH hH0 B hBDG hnull

include hH hH0 B hBDG in
theorem integral_representation (θ : ℝ) (t : ℝ≥0) (ht : t≤H) :
    (fun ω=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap θ (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z₀)
        (FiniteReferenceSplice.jointRows 𝓕 μ H v Rold (Rnew θ)) t :=
  FiniteReferenceSplice.integral_representation 𝓕 μ H v Rold (Rnew θ) J z₀
    (FirstGammaRows.cap (M:=M) Λ κ Z c) (replacementCap Z P c)
    (FirstGammaRows.cap_nonneg Λ κ hκ hell hbU Z c hgap) (replacementCap_nonneg Z P c hgap)
    (FirstGammaRows.actual_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap)
    (replacement_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap θ)
    hH hH0 B hBDG t ht

end SHE.FirstGammaConstruction
