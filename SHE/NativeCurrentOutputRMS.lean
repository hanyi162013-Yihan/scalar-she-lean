module

public import SHE.NativeUniversalConstants

public import SHE.NativeCurrentOutputEnergy
public import SHE.ScalarFibreRMS
public import SHE.MixedPastNativeCurrentEnergy
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

namespace SHE.NativeCurrentOutputRMS
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

private theorem actual_rms {Y:Type*}[MeasurableSpace Y]
    (ν:Measure Y)[SFinite ν](f:Ω×Y→ℝ)(hf:MemLp f 2 (μ.prod ν)):
    ∃a:Y→ℝ,Measurable a ∧ (∀x,0≤a x) ∧ Integrable (fun x=>a x^2) ν ∧
      (∀ᵐx∂ν,MemLp (fun ω=>f (ω,x)) 2 μ ∧ ProfileL2.normTwo μ (fun ω=>f (ω,x))=a x) ∧
      (∫x,a x^2 ∂ν)=∫z,f z^2 ∂μ.prod ν:=by
  let g:=hf.aestronglyMeasurable.mk f
  have hgm:Measurable g:=hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he:f=ᵐ[μ.prod ν] g:=hf.aestronglyMeasurable.ae_eq_mk
  have hgi:MemLp g 2 (μ.prod ν):=MemLp.ae_eq he hf
  have hgs:Integrable (fun z=>|g z|^2) (μ.prod ν):=by simpa only [sq_abs] using hgi.integrable_sq
  let a:=ScalarFibreRMS.rms μ g
  have hr:=ScalarFibreRMS.memLp_energy μ ν g hgm hgs
  refine ⟨a,ScalarFibreRMS.measurable μ g hgm,ScalarFibreRMS.nonneg μ g,hr.1.integrable_sq,?_,?_⟩
  · have hsec:∀ᵐx∂ν,Integrable (fun ω=>g (ω,x)^2) μ:=
      (integrable_prod_iff hgi.integrable_sq.swap.aestronglyMeasurable).mp hgi.integrable_sq.swap |>.1
    have hes:∀ᵐz:Y×Ω∂ν.prod μ,f (z.2,z.1)=g (z.2,z.1):=
      (Measure.measurePreserving_swap (μ:=ν) (ν:=μ)).quasiMeasurePreserving.ae he
    filter_upwards [hsec,Measure.ae_ae_of_ae_prod hes] with x hx heq
    have hgx:MemLp (fun ω=>g (ω,x)) 2 μ:=
      (memLp_two_iff_integrable_sq (hgm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx
    have hreverse:(fun ω=>g (ω,x))=ᵐ[μ](fun ω=>f (ω,x)):=heq.mono (fun _ h=>h.symm)
    refine ⟨MemLp.ae_eq hreverse hgx,?_⟩
    apply congrArg Real.sqrt
    change (∫ω,f (ω,x)^2 ∂μ)=∫ω,|g (ω,x)|^2 ∂μ
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    simp only [hω,sq_abs]
  · have heq:=hr.2
    rw [ProfileL2.normTwo_sq] at heq
    exact heq.trans (integral_congr_ae (he.mono (fun z hz=>by simp only [←hz,sq_abs])))

include hIJ₀ hIJ₁ in
/-- A genuine Borel output RMS of the ACTUAL correlated current packet.
Its pointwise sample norm and sharp total native-output energy are both
derived; no spatially uniform amplitude or independence is used. -/
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
      ∃ aout:HeatCircle→ℝ,Measurable aout ∧ (∀x,0≤aout x) ∧
        Integrable (fun x=>aout x^2) AddCircle.haarAddCircle ∧
        (∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
          MemLp (fun ω=>|Dcur (ω,NativeHeatSpan.unitCenter x)|^χ*G (ω,NativeHeatSpan.unitCenter x)) 2 μ ∧
          ProfileL2.normTwo μ (fun ω=>|Dcur (ω,NativeHeatSpan.unitCenter x)|^χ*G (ω,NativeHeatSpan.unitCenter x))=aout x) ∧
        (∫x:HeatCircle,aout x^2 ∂AddCircle.haarAddCircle)≤
          ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
            Cpacket^(1/(p:ℝ)) :=by
  intro h Cdim
  have hh:=NativeUniversalConstants.currentHorizon_pos.{u} n hn
  have hh1:=NativeUniversalConstants.currentHorizon_le_one.{u} n hn
  have hCdim:=NativeUniversalConstants.currentConstant_pos.{u} n hn
  have he:=NativeCurrentOutputEnergy.actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ n hn
  intro P hΛ hlocal v q hvq hqH hq1 B1 hBDG1 target a t ht hth hage δ hδ hmin
    r m lo hi hdisjoint leaf p hp B0 hBDG χ hχ hχ1 horder G Dcur Cpacket
  have hs:=he P hΛ hlocal v q hvq hqH hq1 B1 hBDG1 target a t ht hth hage δ hδ hmin
    r m lo hi hdisjoint leaf p hp B0 hBDG χ hχ hχ1 horder
  obtain ⟨aout,ham,ha0,hai,hsec,heq⟩:=actual_rms μ AddCircle.haarAddCircle
    (fun z:Ω×HeatCircle=>|Dcur (z.1,NativeHeatSpan.unitCenter z.2)|^χ*G (z.1,NativeHeatSpan.unitCenter z.2)) hs.1
  exact ⟨aout,ham,ha0,hai,hsec,heq.trans_le hs.2⟩

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
      ∃ aout:HeatCircle→ℝ,Measurable aout ∧ (∀x,0≤aout x) ∧
        Integrable (fun x=>aout x^2) AddCircle.haarAddCircle ∧
        (∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
          MemLp (fun ω=>|Dcur (ω,NativeHeatSpan.unitCenter x)|^χ*G (ω,NativeHeatSpan.unitCenter x)) 2 μ ∧
          ProfileL2.normTwo μ (fun ω=>|Dcur (ω,NativeHeatSpan.unitCenter x)|^χ*G (ω,NativeHeatSpan.unitCenter x))=aout x) ∧
        (∫x:HeatCircle,aout x^2 ∂AddCircle.haarAddCircle)≤
          ((Cdim/(3*P.lower/8))*(Real.sqrt δ)⁻¹*(∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ))^χ*
            Cpacket^(1/(p:ℝ)) :=by
  exact ⟨NativeUniversalConstants.currentHorizon.{u} n hn,NativeUniversalConstants.currentConstant.{u} n hn,NativeUniversalConstants.currentHorizon_pos.{u} n hn,NativeUniversalConstants.currentHorizon_le_one.{u} n hn,NativeUniversalConstants.currentConstant_pos.{u} n hn,actual_energy_fixed 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ n hn⟩

end SHE.NativeCurrentOutputRMS
