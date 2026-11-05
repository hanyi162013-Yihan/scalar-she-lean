module

public import SHE.MixedPastNativePacketMoments
public import SHE.NativePacketEnvelope
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativePacketUniform
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativePacketUniform_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativePacketUniform_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativePacketUniform_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativePacketUniform_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativePacketUniform_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativePacketUniform_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastNativePacketUniform_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativePacketUniform_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativePacketUniform_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  NativeFirstWholeMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

/-- The actual current and the full profile mean are affine along the
same theta path. Thus one pair of endpoint budgets controls the entire
current comparison, without taking a supremum of stochastic moments. -/
theorem budget_interpolate (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n)
    (hage:∀j,0<target (leaf j)) (p:ℕ) (θ:ℝ) (hθ:θ∈Set.Icc (0:ℝ) 1) (z:Ω×UnitAddCircle):
    MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P v q σ target a leaf p (θ,z)≤
      (2:ℝ)^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent)*
        (MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P v q σ target a leaf p (0,z)+
          MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            P v q σ target a leaf p (1,z)) := by
  let off:=fun η j=>
    MixedPastNativePacketEnergy.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      v q σ target a (η,z) (leaf j)-ControlledProfile.mean Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.1)
        (η,(target (leaf j),StoppedGaussianScore.nativeCenter (fun i=>a i+z.2) (leaf j)))
  have he : off θ=(fun j=>(1-θ)*off 0 j+θ*off 1 j) := by
    funext j
    simp only [off,MixedPastNativePacketEnergy.meanField,MixedPastJointData.mean,
      WithLp.ofLp_toLp,MixedNativePastThetaCentering.current,ControlledProfile.mean]
    ring
  have hh:=NativePacketEnvelope.budget_interpolate (fun j=>target (leaf j)) (off 0) (off 1)
    θ (((2*(p*(m+2)):ℕ):ℝ)*P.exponent) ((p*(m+2):ℕ)*P.exponent/2) hage hθ
      (mul_nonneg (Nat.cast_nonneg _) P.exponent_pos.le)
  rw [←he] at hh
  convert! hh using 1

def constant (P:CanonicalCovariance.ProfileParameters) (r m p:ℕ):ℝ:=
  NativeFirstWholeComplete.momentConstant P r m p 1+TwoFreshCompleteWord.momentConstant P r m p 1

theorem constant_nonneg (P:CanonicalCovariance.ProfileParameters) (r m p:ℕ):
    0≤constant P r m p:=add_nonneg (NativeFirstWholeComplete.momentConstant_nonneg _ _ _ _ _)
      (TwoFreshCompleteWord.momentConstant_nonneg _ _ _ _ _)

def envelope (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n) (p:ℕ)
    (z:Ω×UnitAddCircle):ℝ:=
  constant P r m p*(1+(2:ℝ)^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent)*
    (MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P v q σ target a leaf p (0,z)+
      MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P v q σ target a leaf p (1,z)))

theorem envelope_nonneg (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n)
    (hage:∀j,0<target (leaf j)) (p:ℕ) (z:Ω×UnitAddCircle):
    0≤envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p z:=by
  apply mul_nonneg (constant_nonneg P r m p)
  have h0:0≤MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P v q σ target a leaf p (0,z):=NormalizedLeafOffsets.budget_nonneg _ _ _ _ hage
  have h1:0≤MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P v q σ target a leaf p (1,z):=NormalizedLeafOffsets.budget_nonneg _ _ _ _ hage
  exact add_nonneg (by norm_num) (mul_nonneg (by positivity) (add_nonneg h0 h1))

theorem constants_le_envelope (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n)
    (hage:∀j,0<target (leaf j)) (p:ℕ) (θ:ℝ) (hθ:θ∈Set.Icc (0:ℝ) 1) (z:Ω×UnitAddCircle):
    let c:=MixedPastNativePacketEnergy.budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P v q σ target a leaf p (θ,z)
    NativeFirstWholeComplete.momentConstant P r m p c≤
        envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p z ∧
      TwoFreshCompleteWord.momentConstant P r m p c≤
        envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p z := by
  intro c
  have hc:0≤c:=NormalizedLeafOffsets.budget_nonneg _ _ _ _ hage
  have hb:=budget_interpolate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P v q σ target a leaf hage p θ hθ z
  have h1c:0≤1+c:=by linarith
  have hd1:NativeFirstWholeComplete.momentConstant P r m p 1≤constant P r m p:=
    le_add_of_nonneg_right (TwoFreshCompleteWord.momentConstant_nonneg _ _ _ _ _)
  have hd2:TwoFreshCompleteWord.momentConstant P r m p 1≤constant P r m p:=
    le_add_of_nonneg_left (NativeFirstWholeComplete.momentConstant_nonneg _ _ _ _ _)
  constructor
  · exact (NativePacketEnvelope.whole_momentConstant P r m p hc).trans
      ((mul_le_mul_of_nonneg_right hd1 h1c).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hb) (constant_nonneg P r m p)))
  · exact (NativePacketEnvelope.marked_momentConstant P r m p hc).trans
      ((mul_le_mul_of_nonneg_right hd2 h1c).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hb) (constant_nonneg P r m p)))

def packet (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n) (p:ℕ)
    (z:Ω×UnitAddCircle):ℝ:=
  (envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p z)^
    (1/((2*p:ℕ):ℝ))

include hIJ₀ hIJ₁ in
/-- The common packet has an actual integer higher moment on the
joint sample/output space. Every stochastic input in this estimate is
derived from the original native equations and past-event BDG. -/
theorem packet_moment (P:CanonicalCovariance.ProfileParameters)
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ)
    (v q:ℝ≥0) (hvq:v≤q) (hqH:q≤H) (hspan:(q:ℝ)-(v:ℝ)≤1)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n)
    (hnative:∀j,σ (leaf j)=target (leaf j)) (hage:∀j,0<target (leaf j))
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i) (p:ℕ) (hp:0<p)
    (B0:ℝ≥0) (hBDG:StandardTerminalBDGPower (p*(m+2)) J B0):
    let G:=packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p
    let C:=(m:ℝ)*(NativeHybridMoments.momentConstant (p*(m+2)) B0 κ M)^P.exponent
    let K:=(2:ℝ)^(((2*(p*(m+2)):ℕ):ℝ)*P.exponent)
    Measurable G ∧ (∀z,0≤G z) ∧ Integrable (fun z=>G z^(2*p)) (μ.prod AddCircle.haarAddCircle) ∧
      (∫z,G z^(2*p) ∂μ.prod AddCircle.haarAddCircle)≤constant P r m p*(1+2*K*C) := by
  intro G C K
  let f0:=fun z:Ω×UnitAddCircle=>MixedPastNativePacketEnergy.budget
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf p (0,z)
  let f1:=fun z:Ω×UnitAddCircle=>MixedPastNativePacketEnergy.budget
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf p (1,z)
  have he0:=MixedPastNativePacketMoments.budget_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ P hlocal hΛ 0 (by norm_num) v q hvq hqH hspan σ target a leaf hnative hage hgap p hp B0 hBDG
  have he1:=MixedPastNativePacketMoments.budget_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ P hlocal hΛ 1 (by norm_num) v q hvq hqH hspan σ target a leaf hnative hage hgap p hp B0 hBDG
  have hm:=MixedPastNativePacketEnergy.budget_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf p hgap
  have hEm:Measurable (envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p):=
    measurable_const.mul (measurable_const.add (measurable_const.mul
      ((hm.comp (measurable_const.prodMk measurable_id)).add
        (hm.comp (measurable_const.prodMk measurable_id)))))
  have hEi:Integrable (envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p)
      (μ.prod AddCircle.haarAddCircle):=
    ((integrable_const 1).add ((he0.1.add he1.1).const_mul K)).const_mul (constant P r m p)
  have hpow(z:Ω×UnitAddCircle):G z^(2*p)=
      envelope 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (r:=r) P v q σ target a leaf p z:=by
    change (_^(1/((2*p:ℕ):ℝ)))^(2*p)=_
    rw [←Real.rpow_mul_natCast (envelope_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P v q σ target a leaf hage p z),one_div_mul_cancel (by positivity : ((2*p:ℕ):ℝ)≠0),Real.rpow_one]
  refine ⟨hEm.pow_const _,(fun z=>Real.rpow_nonneg
    (envelope_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf hage p z) _),
      by simpa only [hpow] using hEi,?_⟩
  simp_rw [hpow]
  change (∫z,constant P r m p*(1+K*(f0 z+f1 z)) ∂μ.prod AddCircle.haarAddCircle)≤_
  have hi0:Integrable f0 (μ.prod AddCircle.haarAddCircle):=he0.1
  have hi1:Integrable f1 (μ.prod AddCircle.haarAddCircle):=he1.1
  have his:Integrable (fun z=>K*(f0 z+f1 z)) (μ.prod AddCircle.haarAddCircle):=by
    convert! (hi0.add hi1).const_mul K using 1
  rw [integral_const_mul,integral_add (integrable_const (1:ℝ)) his,
    integral_const_mul,integral_add hi0 hi1]
  simp only [integral_const,probReal_univ,one_smul]
  apply mul_le_mul_of_nonneg_left _ (constant_nonneg P r m p)
  have hh:=mul_le_mul_of_nonneg_left (add_le_add he0.2 he1.2) (show 0≤K by positivity)
  dsimp [C,f0,f1] at *
  linarith

end SHE.MixedPastNativePacketUniform

