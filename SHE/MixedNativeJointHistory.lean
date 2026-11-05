module

public import SHE.MixedNativeJointObservation
public import SHE.MixedNativePairFuture
public import SHE.NativePairHybridMoments
public import SHE.NativeJointHistory
public import SHE.NativeJointHeatAppend
public import SHE.NativeJointMoments

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativePairHybridMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
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

def displacement (q : ℝ≥0) (T : ℝ) (x : HeatCircle) (θ : ℝ) (ω : Ω) : ℝ :=
  functional (T-(q:ℝ)) x (S.first q ω+θ • (S.second q ω-S.first q ω))-
    (functional T x u₀+θ*Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀))

include hIJ₀ hIJ₁ in
/-- The actual constructed two-channel native pair has the same bounded
all-even current displacement moments as its genuine full-horizon input.
The deterministic damping is at the current time q, with original further
heat target T retained. -/
theorem moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hθ : |θ|≤1)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    (∫⁻ ω,ENNReal.ofReal
      (‖displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q T x θ ω‖^(2*p)) ∂μ) ≤
      ENNReal.ofReal (NativeHybridMoments.momentConstant p B κ M*(q:ℝ)^((p:ℝ)/2)) := by
  have hy := MixedNativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hT x hθ
  have hh := NativeHybridMoments.moment 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ J hqH hq1 p B hBDG
  rw [show (∫⁻ ω,ENNReal.ofReal
      (‖displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q T x θ ω‖^(2*p)) ∂μ) =
      ∫⁻ ω,ENNReal.ofReal (‖J.integral
        (MixedNativePairHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x hΛ hθ) ω‖^(2*p)) ∂μ from
    lintegral_congr_ae (hy.fun_comp (fun z : ℝ => ENNReal.ofReal (‖z‖^(2*p))))]
  exact hh

include hIJ₀ hIJ₁ in
/-- Actual current-state fractional displacement, without Gaussianity
or independence assumptions on the state or the reference profile. -/
theorem fractional_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hθ : |θ|≤1)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q T x θ ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q T x θ ω|^(((2*p:ℕ):ℝ)*β) ∂μ) ≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  have hy := MixedNativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hT x hθ
  have hh := NativeHybridMoments.fractional_moment 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ J hqH hq1 p B hBDG hβ hβ1
  have he : (fun ω => |displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q T x θ ω|^(((2*p:ℕ):ℝ)*β)) =ᵐ[μ]
      fun ω => |J.integral (MixedNativePairHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q hT x hΛ hθ) ω|^(((2*p:ℕ):ℝ)*β) :=
    hy.fun_comp (fun z : ℝ => |z|^(((2*p:ℕ):ℝ)*β))
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans_le hh.2⟩

end SHE.MixedNativePairHybridMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000

namespace SHE.MixedNativeJointHistory
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointHistory_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointHistory_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointHistory_circleSigma : MeasurableSpace CircleL2 := borel _
local instance nativeJointHistory_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

def firstData : PredictableWordState.Data 𝓕 μ H := ⟨Function.uncurry S.first,S.first_predictable⟩
def secondData : PredictableWordState.Data 𝓕 μ H := ⟨Function.uncurry S.second,S.second_predictable⟩

def evaluate {n : ℕ} (Z : Fin n→WordRecursion.Observation) (ω : Ω) (t : ℝ) : WordRecursion.State n :=
  JointWordObserve.evaluate Λ
    (fun r => (firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState (ω,r))
    (fun r => (secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalState (ω,r))
    (fun tx => (firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField (ω,tx))
    (fun tx => (secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).physicalField (ω,tx)) Z t

/-- The actual joint martingale is the physical joint observation used
in recursive words, on every covered positive-gap common window. -/
theorem evaluate_eq_value {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b) (ω : Ω) :
    evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z ω (q:ℝ)=
      MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q ω := by
  apply PiLp.ext
  intro i
  rw [MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap q hqb ω i]
  have hqT : (q:ℝ)<(Z i).target := lt_of_le_of_lt (by exact_mod_cast hqb) (hgap i)
  simp only [evaluate,JointWordObserve.evaluate,WithLp.ofLp_toLp,WordRecursion.observe,ite_eq_left hqT,
    firstData,secondData,PredictableWordState.Data.physicalState,Real.toNNReal_coe,Function.uncurry]
  rw [← functional_physical (sub_pos.mpr hqT),← functional_physical (sub_pos.mpr hqT),map_sub]

/-- Changing the auxiliary covered terminal window never changes any
actual old joint coordinate before both windows. -/
theorem value_common_window_eq {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b c q : ℝ≥0)
    (hbWin : ∀ i,(b:ℝ)<(Z i).target) (hcWin : ∀ i,(c:ℝ)<(Z i).target)
    (hqb : q≤b) (hqc : q≤c) (ω : Ω) :
    MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q ω=
      MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c q ω := by
  exact (evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q hbWin hqb ω).symm.trans
    (evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z c q hcWin hqc ω)

end SHE.MixedNativeJointHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.MixedNativeJointHeatAppend
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointHeatAppend_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointHeatAppend_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {n : ℕ}

def append (Z : Fin n→WordRecursion.Observation) (q ε : ℝ) (x : HeatCircle) : Fin (n+1)→WordRecursion.Observation :=
  Fin.cases ⟨q,q+ε,x⟩ Z

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

/-- Genuine heat-regularized child observation compatibility. The new
original stop is q and its target is q+epsilon, so it equals S_epsilon Vq;
all old joint observations, with their original stops and targets, agree
exactly with the parent window. Epsilon and the time cutoff stay distinct. -/
theorem value_append_heat (Z : Fin n→WordRecursion.Observation) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b) {ε : ℝ} (hε : 0<ε) (x : HeatCircle) (ω : Ω) :
    MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (append Z q ε x) q q ω=
      JointPhysicalInsertion.appendState (functional ε x (S.second q ω))
        (MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q ω) := by
  have hchild : ∀ i,(q:ℝ)<(append Z (q:ℝ) ε x i).target := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact lt_add_of_pos_right _ hε
    · exact lt_of_le_of_lt (by exact_mod_cast hqb) (hgap j)
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hh := MixedNativeJointObservations.value_at_original_stop 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (append Z q ε x) q hchild q le_rfl ω 0 rfl
    change _=functional ε x (S.second q ω)
    simpa only [append,Fin.cases_zero,show (q:ℝ)+ε-(q:ℝ)=ε by ring] using hh
  · have hc := MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (append Z q ε x) q hchild q le_rfl ω j.succ
    have hp := MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      Z b hgap q hqb ω j
    simp only [append,Fin.cases_succ] at hc
    exact hc.trans hp.symm

end SHE.MixedNativeJointHeatAppend

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000

namespace SHE.MixedNativeJointMoments
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b q : ℝ≥0)

def displacement (i : Fin n) (ω : Ω) : ℝ :=
  MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q ω i-
    MixedNativeJointObservations.initial Λ u₀ v₀ Z i

/-- The printed joint mean uses its original stop sigma, not the heat
target T. Its centered actual observation is exactly the honest hybrid
current displacement with theta=exp(-Lambda(sigma-q)). -/
theorem displacement_eq_hybrid (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b) (i : Fin n) (ω : Ω) :
    displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q i ω=
      MixedNativePairHybridMoments.displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        q (Z i).target (Z i).center (Real.exp (-Λ*((Z i).stop-(q:ℝ)))) ω := by
  rw [displacement,MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap q hqb ω i,
    MixedNativeJointObservations.initial_apply]
  unfold MixedNativePairHybridMoments.displacement
  rw [map_add,map_smul]
  have he : Real.exp (-Λ*((Z i).stop-(q:ℝ)))*Real.exp (-Λ*(q:ℝ))=Real.exp (-Λ*(Z i).stop) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change _=_+Real.exp (-Λ*((Z i).stop-(q:ℝ)))*_-
    (_+Real.exp (-Λ*((Z i).stop-(q:ℝ)))*Real.exp (-Λ*(q:ℝ))*_)
  rw [he]

theorem weight_bound (hΛ : 0≤Λ) (i : Fin n) (hstop : (q:ℝ)≤(Z i).stop) :
    |Real.exp (-Λ*((Z i).stop-(q:ℝ)))|≤1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr hstop)

include hIJ₀ hIJ₁ in
/-- All-even moments of actual drift-cancelling joint observations
around their literal printed mean, uniformly over future original stops
and arbitrary further heat targets. No Gaussian current-state premise. -/
theorem moment (hΛ : 0≤Λ) (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b)
    (hqH : q≤H) (hq1 : (q:ℝ)≤1) (i : Fin n) (hstop : (q:ℝ)≤(Z i).stop)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    (∫⁻ ω,ENNReal.ofReal (‖displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q i ω‖^(2*p)) ∂μ)≤
      ENNReal.ofReal (NativeHybridMoments.momentConstant p B κ M*(q:ℝ)^((p:ℝ)/2)) := by
  have hqT : (q:ℝ)<(Z i).target := lt_of_le_of_lt (by exact_mod_cast hqb) (hgap i)
  have hh := MixedNativePairHybridMoments.moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hqT (Z i).center (weight_bound Λ Z q hΛ i hstop) p B hBDG
  simpa only [displacement_eq_hybrid 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q hgap hqb i] using hh

include hIJ₀ hIJ₁ in
theorem fractional_moment (hΛ : 0≤Λ) (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b)
    (hqH : q≤H) (hq1 : (q:ℝ)≤1) (i : Fin n) (hstop : (q:ℝ)≤(Z i).stop)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q i ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q i ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  have hqT : (q:ℝ)<(Z i).target := lt_of_le_of_lt (by exact_mod_cast hqb) (hgap i)
  have hh := MixedNativePairHybridMoments.fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    hΛ q hqH hq1 hqT (Z i).center (weight_bound Λ Z q hΛ i hstop) p B hBDG hβ hβ1
  simpa only [displacement_eq_hybrid 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q hgap hqb i] using hh

end SHE.MixedNativeJointMoments
