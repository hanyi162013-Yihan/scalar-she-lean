module

public import SHE.MixedNativePairObservation
public import SHE.NativePairHybridIdentity
public import SHE.NativePairFutureMean
public import SHE.NativePairFutureMoments

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.MixedNativePairHybridIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairHybridIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairHybridIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairHybridIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairHybridIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairHybridIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairHybridIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def input (q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle)
    (hΛ : 0≤Λ) {θ : ℝ} (hθ : |θ|≤1) : Process (E := Both RealHaarInput) 𝓕 μ H :=
  NativeHybridInput.input 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ

include hIJ₀ hIJ₁ in
/-- The actual native current interpolation, centered at its current-time
deterministic heat mean, is exactly the full-horizon hybrid scalar Itô
integral. This identifies the moment input with the constructed pair. -/
theorem centered_current (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H) {T : ℝ}
    (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hθ : |θ|≤1) :
    (fun ω => functional (T-(q:ℝ)) x (S.first q ω+θ • (S.second q ω-S.first q ω))-
      (functional T x u₀+θ*Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀)))=ᵐ[μ]
      J.integral (input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x hΛ hθ) := by
  let D := NativeHybridInput.dampedDifference 𝓕 μ H hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ
  let R := MixedNativePairObservedFirst.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x
  have he := NativeHybridInput.integral_eq 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ J
  change J.integral (input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x hΛ hθ)=
    J.integral R+θ • (rightIntegral 𝓕 μ H J).integral D at he
  have hadd := Lp.coeFn_add (J.integral R) (θ • (rightIntegral 𝓕 μ H J).integral D)
  rw [← he] at hadd
  filter_upwards [MixedNativePairObservedFirst.observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ q hq hT x,
    MixedNativePairResolvent.difference_observation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq hT x,
    hadd,Lp.coeFn_smul θ ((rightIntegral 𝓕 μ H J).integral D)] with ω hfirst hdiff hadd hsmul
  rw [map_add,map_smul,hfirst,hdiff,hadd]
  change _=J.integral R ω+(θ • (rightIntegral 𝓕 μ H J).integral D) ω
  rw [hsmul]
  change _=J.integral R ω+θ*(rightIntegral 𝓕 μ H J).integral D ω
  ring

end SHE.MixedNativePairHybridIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.MixedNativePairFutureMean
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans StoppedGaussianFeatures StoppedGaussianScore
open scoped NNReal ENNReal
local instance nativePairFutureMean_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairFutureMean_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairFutureMean_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativePairFutureMean_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairFutureMean_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairFutureMean_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairFutureMean_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

theorem reference_state_observation (Λ : ℝ) (q : ℝ≥0) (u d : RealL2) (θ : ℝ)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    physicalHeatMean (referenceState Λ q q.2 (embed u) (embed d) θ) (T-(q:ℝ),x)=
      functional T x u+θ*Real.exp (-Λ*(q:ℝ))*functional T x d := by
  have hr := sub_pos.mpr hT
  have ht : 0<T := q.2.trans_lt hT
  rw [referenceState,heatMean_add hr,heatMean_smul hr,
    heatMean_heat (r := T-(q:ℝ)) (q := (q:ℝ)) hr (show 0≤(q:ℝ) from q.2),
    heatMean_heat (r := T-(q:ℝ)) (q := (q:ℝ)) hr (show 0≤(q:ℝ) from q.2),
    show (q:ℝ)+(T-(q:ℝ))=T by ring,← functional_physical ht,← functional_physical ht]

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

include hIJ₀ hIJ₁ in
/-- The actual compensated conditional future mean, centered at the
printed controlled profile mean (damping at each original target), is
the genuine same-driver hybrid stochastic integral. The compensator
retains the distinct current-time damping exactly. -/
theorem future_mean_displacement (hΛ : 0≤Λ) (q : ℝ≥0) (hq : q≤H)
    {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hgap : ∀ i,(q:ℝ)<target i) {θ : ℝ} (hθ : |θ|≤1) :
    ∀ᵐ ω ∂μ,∀ i,
      futureMeanVector Λ target centers q q.2 (embed u₀) (embed (v₀-u₀))
        (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ i-
        ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀))
          (θ,(target i,nativeCenter centers i))=
        J.integral (MixedNativePairHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          q (hgap i) (nativeCenter centers i) hΛ hθ) ω := by
  have hh (i : Fin n) := MixedNativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ q hq (hgap i) (nativeCenter centers i) hθ
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  intro i
  change physicalHeatMean (embed (S.first q ω)+θ • embed (S.second q ω-S.first q ω))
    (target i-(q:ℝ),nativeCenter centers i)+
    ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (θ,(target i,nativeCenter centers i))-
    physicalHeatMean (referenceState Λ q q.2 (embed u₀) (embed (v₀-u₀)) θ)
      (target i-(q:ℝ),nativeCenter centers i)-
    ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (θ,(target i,nativeCenter centers i))=_
  have he : embed (S.first q ω+θ • (S.second q ω-S.first q ω))=
      embed (S.first q ω)+θ • embed (S.second q ω-S.first q ω) := by rw [map_add,map_smul]
  rw [← he,← functional_physical (sub_pos.mpr (hgap i)),
    reference_state_observation Λ q u₀ (v₀-u₀) θ (hgap i)]
  convert hω i using 1 <;> ring

end SHE.MixedNativePairFutureMean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativePairFutureMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def displacement (q : ℝ≥0) {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (θ : ℝ) (i : Fin n) (ω : Ω) : ℝ :=
  futureMeanVector Λ target centers q q.2 (embed u₀) (embed (v₀-u₀))
    (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ i-
    ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (θ,(target i,nativeCenter centers i))

include hIJ₀ hIJ₁ in
/-- Actual compensated future means are centered at the printed
controlled profile, at every original target. Their all fixed fractional
moments follow from the genuine same-driver hybrid integral; current
states are not asserted to be Gaussian or independent of the profile. -/
theorem fractional_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hgap : ∀ i,(q:ℝ)<target i) {θ : ℝ} (hθ : |θ|≤1)
    (i : Fin n) (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q target centers θ i ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q target centers θ i ω|^(((2*p:ℕ):ℝ)*β) ∂μ) ≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  have hy := MixedNativePairFutureMean.future_mean_displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH target centers hgap hθ
  have hh := NativeHybridMoments.fractional_moment 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q (hgap i) (nativeCenter centers i) hΛ hθ J hqH hq1 p B hBDG hβ hβ1
  have he : (fun ω => |displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q target centers θ i ω|^(((2*p:ℕ):ℝ)*β)) =ᵐ[μ]
      fun ω => |J.integral (MixedNativePairHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        q (hgap i) (nativeCenter centers i) hΛ hθ) ω|^(((2*p:ℕ):ℝ)*β) := by
    filter_upwards [hy] with ω hω
    exact congrArg (fun z : ℝ => |z|^(((2*p:ℕ):ℝ)*β)) (hω i)
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans_le hh.2⟩

end SHE.MixedNativePairFutureMoments
