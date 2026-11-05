module

public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
public import SHE.FirstGammaFrozenValues
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

namespace SHE.FirstGammaCurrentIdentity
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaCurrentIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaCurrentIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaCurrentIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaCurrentIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaCurrentIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaCurrentIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaCurrentIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaCurrentIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

private theorem exp_cancel (Λ t : ℝ) : Real.exp (-Λ*t)*Real.exp (Λ*t)=1 := by
  rw [←Real.exp_add,show -Λ*t+Λ*t=0 by ring,Real.exp_zero]

private theorem exp_shift (Λ t v : ℝ) :
    Real.exp (-Λ*t)*Real.exp (Λ*v)=Real.exp (-Λ*(t-v)) := by
  rw [←Real.exp_add]
  congr 1
  ring

include hH hH0 B hBDG hIJ₀ hIJ₁ in
/-- The finite affine current is exactly the printed corrected future
mean, including the remaining deterministic forcing from the OLD past. -/
theorem current_eq_corrected (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hvq : v≤q) (hqc : q≤c) :
    ∀ᵐ ω∂μ,∀ i,
      FirstGammaAffine.current n Λ θ (fun i=>(Z i).target) q (Y θ (q,ω)) i=
        functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
          θ*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω)+
          θ*(Real.exp (-Λ*((Z i).target-(v:ℝ)))-Real.exp (-Λ*((q:ℝ)-(v:ℝ))))*
            functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω) := by
  filter_upwards [FirstGammaValues.currentU_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
      hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hqc,
    FirstGammaValues.currentD_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
      hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hqc,
    FirstGammaFrozenValues.pastD_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
      hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hvq hqc] with ω hu hd hp i
  simp only [FirstGammaAffine.current,DampedAffineGaussian.linear,FirstGammaAffine.baseCurrent,FirstGammaAffine.dynamic,
    add_apply,smul_apply,ContinuousLinearMap.comp_apply,sub_apply,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,
    smul_eq_mul,FirstGammaAffine.terminalDamping_apply,ClippedExponential.coefficient,ClippedExponential.damping,max_eq_left (show 0≤(q:ℝ) from q.2)]
  rw [hu i,hd i,hp i]
  have he:=exp_cancel Λ (q:ℝ)
  have ht:=exp_shift Λ (Z i).target (v:ℝ)
  have hq:=exp_shift Λ (q:ℝ) (v:ℝ)
  linear_combination θ*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω)*he+
  θ*functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)*ht-
  θ*functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)*hq

include hH hH0 B hBDG hIJ₀ hIJ₁ in
/-- The actual control drift remains in the finite-Itô identity. It is
not removed by replacing the corrected current with a stopped joint martingale. -/
theorem current_derivative_eq (θ : ℝ) (hcH : c≤H) (q : ℝ≥0) (hvq : v≤q) (hqc : q≤c) :
    ∀ᵐ ω∂μ,∀ i,
      FirstGammaAffine.currentDerivative n Λ θ q (Y θ (q,ω)) i=
        -Λ*θ*(functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω)-
          Real.exp (-Λ*((q:ℝ)-(v:ℝ)))*
            functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)) := by
  filter_upwards [FirstGammaValues.currentD_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
      hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hqc,
    FirstGammaFrozenValues.pastD_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
      hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH q hvq hqc] with ω hd hp i
  simp only [FirstGammaAffine.currentDerivative,DampedAffineGaussian.linearDerivative,FirstGammaAffine.dynamic,
    smul_apply,sub_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
    ClippedExponential.coefficient,ClippedExponential.damping,max_eq_left (show 0≤(q:ℝ) from q.2)]
  rw [hd i,hp i]
  have he:=exp_cancel Λ (q:ℝ)
  have hq:=exp_shift Λ (q:ℝ) (v:ℝ)
  linear_combination -Λ*θ*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω)*he+
  Λ*θ*functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)*hq

end SHE.FirstGammaCurrentIdentity
