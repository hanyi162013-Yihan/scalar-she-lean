module

public import SHE.NativeUniversalConstants

public import SHE.MixedPastNativePacketUniform
public import SHE.MixedNativeDampedScoreAmplitude
public import SHE.CorrelatedCurrentHolder
public import SHE.MixedPastNativeFirstWholeCompleteWeights
public import SHE.MixedPastTwoFreshCompleteWeights
public import SHE.ControlledFutureFields
public import SHE.SectionEnergy
public import SHE.NativeFirstWholeComplete
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section
universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeCurrentEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeCurrentEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeCurrentEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeCurrentEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeCurrentEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeCurrentEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeCurrentEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastNativeCurrentEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type u} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativeCurrentEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeCurrentEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  NativeFirstWholeMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- Actual correlated current-packet energy. Only the distinguished
current Dq uses its second moment; all other scores and offsets remain
in the single actual higher-moment packet. -/
theorem actual_energy_fixed (n:ℕ) (hn:0<n):
    let h:=NativeUniversalConstants.currentHorizon.{u} n hn
    let Cdim:=NativeUniversalConstants.currentConstant.{u} n hn
    ∀(P:CanonicalCovariance.ProfileParameters),0<Λ→
      StandardTerminalPastLocality J→∀(v q:ℝ≥0),v≤q→q≤H→(q:ℝ)≤1→
      ∀(B1:ℝ≥0),StandardTerminalBDGPower 1 J B1→
      ∀(target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (t:Fin n→ℝ),
      (∀i,0<t i)→(∀i,t i≤h)→(∀i,target i-((q:ℝ)-(v:ℝ))=4*Real.pi^2*t i)→
      ∀(δ:ℝ),0<δ→(∀i,(q:ℝ)-(v:ℝ)+δ≤target i)→
      ∀(r m:ℕ) (lo hi:Fin r→ℝ),(∀j k,j≠k→hi j≤lo k ∨ hi k≤lo j)→
      ∀(leaf:Fin m→Fin n) (p:ℕ),0<p→
      ∀(B0:ℝ≥0),StandardTerminalBDGPower (p*(m+2)) J B0→
      ∀(χ:ℝ),0≤χ→χ<1→1≤(p:ℝ)*(1-χ)→
      let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ u₀ S (r:=r) P v q target target a leaf p
      let Dcur:=MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ S P v q target a lo hi
      let Cpacket:=MixedPastNativePacketUniform.constant P r m p*
        (1+2*(2:ℝ)^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent)*
          ((m:ℝ)*(NativeHybridMoments.momentConstant (p*(m+2)) B0 κ M)^P.exponent))
      MemLp (fun z=>|Dcur z|^χ*G z) 2 (μ.prod AddCircle.haarAddCircle) ∧
        (∫z,(|Dcur z|^χ*G z)^2 ∂μ.prod AddCircle.haarAddCircle)≤
          ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
            Cpacket^(1/(p:ℝ)) :=by
  intro h Cdim
  have hh:=NativeUniversalConstants.currentHorizon_pos.{u} n hn
  have hh1:=NativeUniversalConstants.currentHorizon_le_one.{u} n hn
  have hCdim:=NativeUniversalConstants.currentConstant_pos.{u} n hn
  have he:=MixedNativeDampedScoreAmplitude.actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ n hn
  intro P hΛ hlocal v q hvq hqH hq1 B1 hBDG1 target a t ht hth hage δ hδ hmin
    r m lo hi hdisjoint leaf p hp B0 hBDG χ hχ hχ1 horder G Dcur Cpacket
  have hgap(i:Fin n):(q:ℝ)-(v:ℝ)<target i:=lt_of_lt_of_le (by linarith : (q:ℝ)-(v:ℝ)<(q:ℝ)-(v:ℝ)+δ) (hmin i)
  have hpositive(i:Fin n):0<target i:=(sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)).trans_lt (hgap i)
  have hspan:(q:ℝ)-(v:ℝ)≤1:=by linarith [v.2]
  have hD:=he P hΛ v q hqH hq1 B1 hBDG1 target a t ht hth hage δ hδ hmin r lo hi hdisjoint
  have hG:=MixedPastNativePacketUniform.packet_moment (r:=r) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P hlocal hΛ.le v q hvq hqH hspan target target a leaf
    (fun _=>rfl) (fun j=>hpositive (leaf j)) hgap p hp B0 hBDG
  have hGi:Integrable (fun z=>G z^(2*p)) (μ.prod AddCircle.haarAddCircle):=hG.2.2.1
  have hGb:(∫z,G z^(2*p) ∂μ.prod AddCircle.haarAddCircle)≤Cpacket:=hG.2.2.2
  have hCn:0≤Cpacket:=(integral_nonneg (fun z=>pow_nonneg (hG.2.1 z) _)).trans hGb
  have hMoment:(∫⁻z,ENNReal.ofReal (‖G z‖^(2*p)) ∂μ.prod AddCircle.haarAddCircle)≤ENNReal.ofReal Cpacket:=by
    have heq:=ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ (fun z=>pow_nonneg (hG.2.1 z) _))
    have hnorm(z:Ω×UnitAddCircle):‖G z‖^(2*p)=G z^(2*p):=by rw [Real.norm_of_nonneg (hG.2.1 z)]
    simp_rw [hnorm]
    exact heq.symm.trans_le (ENNReal.ofReal_le_ofReal hGb)
  have hc:=CorrelatedCurrentHolder.energy_of_even_moment Dcur G hD.2.2.2.2.1 hG.1.aestronglyMeasurable
    hχ hχ1 hCn p hp horder hMoment
  refine ⟨hc.1,hc.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (integral_nonneg (fun z=>sq_nonneg (Dcur z))) hD.2.2.2.2.2 hχ)
    (Real.rpow_nonneg hCn _)

include hIJ₀ hIJ₁ in
theorem actual_energy (n:ℕ) (hn:0<n):
    ∃ h Cdim:ℝ,0<h ∧ h≤1 ∧ 0<Cdim ∧
      ∀(P:CanonicalCovariance.ProfileParameters),0<Λ→
      StandardTerminalPastLocality J→∀(v q:ℝ≥0),v≤q→q≤H→(q:ℝ)≤1→
      ∀(B1:ℝ≥0),StandardTerminalBDGPower 1 J B1→
      ∀(target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (t:Fin n→ℝ),
      (∀i,0<t i)→(∀i,t i≤h)→(∀i,target i-((q:ℝ)-(v:ℝ))=4*Real.pi^2*t i)→
      ∀(δ:ℝ),0<δ→(∀i,(q:ℝ)-(v:ℝ)+δ≤target i)→
      ∀(r m:ℕ) (lo hi:Fin r→ℝ),(∀j k,j≠k→hi j≤lo k ∨ hi k≤lo j)→
      ∀(leaf:Fin m→Fin n) (p:ℕ),0<p→
      ∀(B0:ℝ≥0),StandardTerminalBDGPower (p*(m+2)) J B0→
      ∀(χ:ℝ),0≤χ→χ<1→1≤(p:ℝ)*(1-χ)→
      let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ u₀ S (r:=r) P v q target target a leaf p
      let Dcur:=MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ S P v q target a lo hi
      let Cpacket:=MixedPastNativePacketUniform.constant P r m p*
        (1+2*(2:ℝ)^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent)*
          ((m:ℝ)*(NativeHybridMoments.momentConstant (p*(m+2)) B0 κ M)^P.exponent))
      MemLp (fun z=>|Dcur z|^χ*G z) 2 (μ.prod AddCircle.haarAddCircle) ∧
        (∫z,(|Dcur z|^χ*G z)^2 ∂μ.prod AddCircle.haarAddCircle)≤
          ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
            Cpacket^(1/(p:ℝ)) :=by
  exact ⟨NativeUniversalConstants.currentHorizon.{u} n hn,NativeUniversalConstants.currentConstant.{u} n hn,NativeUniversalConstants.currentHorizon_pos.{u} n hn,NativeUniversalConstants.currentHorizon_le_one.{u} n hn,NativeUniversalConstants.currentConstant_pos.{u} n hn,actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ n hn⟩

end SHE.MixedPastNativeCurrentEnergy

