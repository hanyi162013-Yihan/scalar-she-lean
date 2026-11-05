module

public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FiniteReferenceSplicePast
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

namespace SHE.MixedNativeFrozenPrefixValues
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeFrozenPrefixValues_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeFrozenPrefixValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeFrozenPrefixValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeFrozenPrefixValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeFrozenPrefixValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeFrozenPrefixValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeFrozenPrefixValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeFrozenPrefixValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open MixedNativeFrozenPrefixIto
local notation "Rold" => actualRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "Rnew" => frozenRows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativeJointObservations.initial Λ u₀ v₀ Z
local notation "Y" => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap

/-- The genuine splice vector is represented by the original scalar J
at every covered time. All bounds are discharged by the native model. -/
theorem joint_representation (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0)
    (hBDG : StandardTerminalBDG16 J B) (hstop : ∀ i,(c:ℝ)≤(Z i).stop)
    (t : ℝ≥0) (htH : t≤H) :
    (fun ω => Y (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z₀)
        (FiniteReferenceSplice.jointRows 𝓕 μ H v Rold Rnew) t := by
  let K : Fin n→ℝ := fun i => NativeObservationCaps.cap (κ+10*M) ((Z i).target-(c:ℝ))
  let L : Fin n→ℝ := fun i => NativeObservationCaps.cap P.upper ((Z i).target-(c:ℝ))
  have hm : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hK : ∀ i,0≤K i := fun i => NativeObservationCaps.cap_nonneg (by positivity) (sub_pos.mpr (hgap i))
  have hL : ∀ i,0≤L i := fun i => NativeObservationCaps.cap_nonneg P.upper_nonneg (sub_pos.mpr (hgap i))
  exact FiniteReferenceSplice.integral_representation 𝓕 μ H v Rold Rnew J z₀ K L hK hL
    (MixedNativeJointCaps.clippedRows_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap hstop)
    (PastFrozenPrefixRows.rows_bound 𝓕 μ H P Λ κ 1 hκ hκP v
      (data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v)
      (data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) Z c hgap)
    hH hH0 B hBDG t htH

variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
theorem original_representation (hcH : c≤H) (t : ℝ≥0) (ht : t≤c) :
    MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c t=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z₀ Rold t := by
  have hh := MixedNativeJointObservations.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z c hgap hΛ hcH t
  have he : StandardFiniteIto.vectorIntegral 𝓕 μ H J z₀ Rold t=
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z₀
        (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap hΛ) t := by
    funext ω
    apply PiLp.ext
    intro i
    change z₀ i+J.integral (StoppedItoInputs.stop 𝓕 μ H (t:ℝ) (Rold i)) ω=_
    rw [actualRows,MixedNativeJointCaps.clippedRows,StoppedIntegralVersions.stop_stop,
      min_eq_left (show (t:ℝ)≤(c:ℝ) by exact_mod_cast ht)]
    rfl
  rw [he]
  exact hh


include hIJ₀ hIJ₁ in
/-- Left coordinates are literally the actual original-stop joint
current fields, not a surrogate Gaussian process. -/
theorem left_eq_current (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0)
    (hBDG : StandardTerminalBDG16 J B) (hstop : ∀ i,(c:ℝ)≤(Z i).stop)
    (hcH : c≤H) (q : ℝ≥0) (hqc : q≤c) :
    ∀ᵐ ω ∂μ,∀ i,
      Y (q,ω) (Fin.castAdd n i)=
        functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
        Real.exp (-Λ*((Z i).stop-(q:ℝ)))*functional ((Z i).target-(q:ℝ)) (Z i).center
          (S.second q ω-S.first q ω) := by
  filter_upwards [joint_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hstop q (hqc.trans hcH),
    original_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J hΛ c hgap hIJ₀ hIJ₁ hcH q hqc]
    with ω hj ho i
  rw [hj,←MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap q hqc ω i,ho]
  simp only [StandardFiniteIto.vectorIntegral,FiniteReferenceSplice.jointInitial,
    FiniteReferenceSplice.jointRows,WithLp.ofLp_toLp,Fin.append_left]

include hIJ₀ hIJ₁ in
/-- Right coordinates retain the exact random F_v current mean and
then integrate the literal post-v frozen rows of the SAME full-H J. -/
theorem right_eq_frozen (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0)
    (hBDG : StandardTerminalBDG16 J B) (hstop : ∀ i,(c:ℝ)≤(Z i).stop)
    (hcH : c≤H) (hvc : v≤c) (q : ℝ≥0) (hvq : v≤q) (hqc : q≤c) :
    ∀ᵐ ω ∂μ,∀ i,
      Y (q,ω) (Fin.natAdd n i)=
        (functional ((Z i).target-(v:ℝ)) (Z i).center (S.first v ω)+
          Real.exp (-Λ*((Z i).stop-(v:ℝ)))*functional ((Z i).target-(v:ℝ)) (Z i).center
            (S.second v ω-S.first v ω))+
        J.integral (StoppedItoInputs.stop 𝓕 μ H (q:ℝ) (PastItoInputs.post 𝓕 μ H v (Rnew i))) ω := by
  filter_upwards [joint_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hstop q (hqc.trans hcH),
    original_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J hΛ c hgap hIJ₀ hIJ₁ hcH v hvc,
    FiniteReferenceSplice.integral_after_past 𝓕 μ H v Rold Rnew J z₀ q hvq] with ω hj ho hf i
  rw [hj,←MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c hgap v hvc ω i,ho]
  have hfi := congrArg (fun z : WordRecursion.State n => z i) hf
  simpa only [StandardFiniteIto.vectorIntegral,FiniteReferenceSplice.jointInitial,
    FiniteReferenceSplice.jointRows,WithLp.ofLp_toLp,Fin.append_right,PiLp.add_apply] using hfi

end SHE.MixedNativeFrozenPrefixValues
