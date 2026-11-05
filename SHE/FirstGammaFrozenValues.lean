module

public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
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

namespace SHE.FirstGammaFrozenValues
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
/-- The replacement half of the finite vector is the exact original
past observation plus the original post-v frozen integral. -/
theorem right_eq_reference (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hvq : v≤q) (hqc : q≤c) :
    (fun ω=>FiniteComparisonTest.right (n+n) (Y θ (q,ω)))=ᵐ[μ]
      fun ω=>MixedNativePairExtendedMartingale.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (fun i=>(Z i).target) (fun i=>(Z i).center) c v ω+
          WithLp.toLp 2 (fun i=>J.integral (StoppedItoInputs.stop 𝓕 μ H (q:ℝ)
            (PastItoInputs.post 𝓕 μ H v (Rnew θ i))) ω) := by
  filter_upwards [FirstGammaConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap hH hH0 B hBDG θ q (hqc.trans hcH),
    MixedNativePairExtendedMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ (fun i=>(Z i).target) (fun i=>(Z i).center) c hgap hΛ hcH v,
    FiniteReferenceSplice.integral_after_past 𝓕 μ H v Rold (Rnew θ) J z₀ q hvq]
    with ω hj ho hf
  rw [hj,ho]
  apply PiLp.ext
  intro i
  have hfi:=congrArg (fun z : WordRecursion.State (n+n)=>z i) hf
  simpa only [FiniteComparisonTest.right_apply,StandardFiniteIto.vectorIntegral,
    FiniteReferenceSplice.jointInitial,FiniteReferenceSplice.jointRows,WithLp.ofLp_toLp,Fin.append_right,PiLp.add_apply,
    FirstGammaRows.actual] using hfi

theorem zero_replacement_noise (θ : ℝ) (q : ℝ≥0) (i : Fin n) :
    J.integral (StoppedItoInputs.stop 𝓕 μ H (q:ℝ)
      (PastItoInputs.post 𝓕 μ H v (Rnew θ (Fin.natAdd n i))))=0 := by
  have hp : PastItoInputs.post 𝓕 μ H v (Rnew θ (Fin.natAdd n i))=0 := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [PastItoInputs.post_ae 𝓕 μ H v (Rnew θ (Fin.natAdd n i)),
      ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
        ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hp hz
    rw [hp]
    simp only [FirstGammaRows.replacement,Fin.append_right,hz,Pi.zero_apply]
    split_ifs <;> rfl
  have hs : StoppedItoInputs.stop 𝓕 μ H (q:ℝ) (0:Process (E:=Both RealHaarInput) 𝓕 μ H)=0 := by
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [StoppedItoInputs.stop_ae 𝓕 μ H (q:ℝ) (0:Process (E:=Both RealHaarInput) 𝓕 μ H),
      ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
        ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hs hz
    rw [hs]
    by_cases hmem : p∈StoppedItoInputs.before (Ω:=Ω) (q:ℝ)
    · rw [Set.indicator_of_mem hmem,hz]
    · rw [Set.indicator_of_notMem hmem]
      exact hz.symm
  rw [hp,hs,map_zero]

include hH hH0 B hBDG hIJ₀ hIJ₁ in
/-- The old rescaled controlled difference is literally frozen. -/
theorem pastD_eq (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hvq : v≤q) (hqc : q≤c) :
    ∀ᵐ ω∂μ,∀ i,FirstGammaAffine.pastD n (Y θ (q,ω)) i=
      Real.exp (Λ*(v:ℝ))*functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω) := by
  have hn (i : Fin n) : ∀ᵐ ω∂μ,J.integral (StoppedItoInputs.stop 𝓕 μ H (q:ℝ)
      (PastItoInputs.post 𝓕 μ H v (Rnew θ (Fin.natAdd n i)))) ω=0 := by
    rw [zero_replacement_noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP v c hgap θ q i]
    exact Lp.coeFn_zero ℝ 2 μ
  filter_upwards [right_eq_reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hvq hqc,ae_all_iff.mpr hn] with ω hω hn i
  change ObservationBlockMaps.second n (FiniteComparisonTest.right (n+n) (Y θ (q,ω))) i=_
  rw [hω]
  simp only [ObservationBlockMaps.second_apply,PiLp.add_apply,WithLp.ofLp_toLp,hn i,add_zero,
    MixedNativePairExtendedMartingale.value,Fin.append_right,MixedNativePairLocalMartingale.value,
    min_eq_left (hvq.trans hqc)]
  rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
      (sub_le_sub_left (by exact_mod_cast hvq.trans hqc) _),
    PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
      (sub_le_sub_left (by exact_mod_cast hvq.trans hqc) _),map_sub]
  rfl

end SHE.FirstGammaFrozenValues
