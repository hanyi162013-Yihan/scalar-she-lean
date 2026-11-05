module

public import SHE.MixedNativeJointCaps
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

namespace SHE.MixedNativeFrozenPrefixIto
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeFrozenPrefixIto_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeFrozenPrefixIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeFrozenPrefixIto_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeFrozenPrefixIto_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeFrozenPrefixIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeFrozenPrefixIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeFrozenPrefixIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeFrozenPrefixIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

/-- Actual F_v states frozen for the reference. -/
def data (ω : Ω) : ControlledProfile.Inputs :=
  (embed (S.first v ω),embed (S.second v ω-S.first v ω))

theorem data_measurable : Measurable[𝓕 v] (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) :=
  (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).prodMk
    (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)

def actualRows : Fin n → Process (E:=Both RealHaarInput) 𝓕 μ H :=
  MixedNativeJointCaps.clippedRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap hΛ

def frozenRows : Fin n → Process (E:=Both RealHaarInput) 𝓕 μ H :=
  PastFrozenPrefixRows.rows 𝓕 μ H P Λ κ 1 hκ hκP v
    (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
    (data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) Z c hgap

/-- One genuine finite vector contains the original joint observation
and its same-driver, actual-random-past frozen reference. -/
def value : ℝ≥0×Ω → WordRecursion.State (n+n) :=
  FiniteReferenceSplice.value 𝓕 μ H v
    (actualRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap)
    (frozenRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap)
    J (MixedNativeJointObservations.initial Λ u₀ v₀ Z)

/-- The ordinary package-2 finite Ito formula applies to the literal
constructed current/reference vector. All row caps and random-reference
predictability are derived from the actual mixed solution and actual
canonical profile. This is a positive-gap prefix statement; no random
Gaussian test is silently admitted to the deterministic formula. -/
theorem finiteItoInput (hH : (H:ℝ)≤1) (hH0 : 0<H)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
    (hvc : v≤c) (hcH : c≤H) (hstop : ∀ i,(c:ℝ)≤(Z i).stop) :
    ∃ N : (ℝ→WordRecursion.State (n+n)→ℝ)→Ω→ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω t => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap (t.toNNReal,ω))
        (StandardFiniteIto.rowCovariance 𝓕 μ H
          (FiniteReferenceSplice.jointRows 𝓕 μ H v
            (actualRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap)
            (frozenRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap))) v c N := by
  let K : Fin n→ℝ := fun i => NativeObservationCaps.cap (κ+10*M) ((Z i).target-(c:ℝ))
  let L : Fin n→ℝ := fun i => NativeObservationCaps.cap P.upper ((Z i).target-(c:ℝ))
  have hm : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hK : ∀ i,0≤K i := fun i => NativeObservationCaps.cap_nonneg (by positivity) (sub_pos.mpr (hgap i))
  have hL : ∀ i,0≤L i := fun i => NativeObservationCaps.cap_nonneg P.upper_nonneg (sub_pos.mpr (hgap i))
  exact FiniteReferenceSplice.finiteItoInput 𝓕 μ H v
    (actualRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap)
    (frozenRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap)
    J hH hH0 hnull B hBDG hJ (MixedNativeJointObservations.initial Λ u₀ v₀ Z) K L hK hL
    (MixedNativeJointCaps.clippedRows_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap hstop)
    (PastFrozenPrefixRows.rows_bound 𝓕 μ H P Λ κ 1 hκ hκP v
      (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
      (data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) Z c hgap) c hvc hcH

end SHE.MixedNativeFrozenPrefixIto
