module

public import SHE.NativeJointMoments
public import SHE.NativeJointHistory
public import SHE.MixedNativeJointHistory
public import SHE.ControlledProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.NativeJointMeanDisplacement
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance jointMeanDisplacementLocal1 : Fact (0<2*π) := ⟨by positivity⟩
local instance jointMeanDisplacementLocal2 : MeasurableSpace RealL2 := borel _
local instance jointMeanDisplacementLocal3 : BorelSpace RealL2 := ⟨rfl⟩
local instance jointMeanDisplacementLocal4 : MeasurableSpace RealHaarInput := borel _
local instance jointMeanDisplacementLocal5 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointMeanDisplacementLocal6 : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointMeanDisplacementLocal7 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def current (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) (ω : Ω) : GaussianIncrement.State n :=
  WithLp.toLp 2 (fun i => functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
    Real.exp (-Λ*((Z i).stop-(q:ℝ)))*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω))

theorem current_measurable (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) :
    Measurable (current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  simp_rw [map_sub]
  exact ((functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hU).add
    ((((functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hV).sub
      ((functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hU)).const_mul _)

theorem current_eq_value (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hgap : ∀ i,(q:ℝ)<(Z i).target) (ω : Ω) :
    current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q ω=
      NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q q ω := by
  apply PiLp.ext
  intro i
  exact (NativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q hgap q le_rfl ω i).symm

theorem current_eq_evaluate (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hgap : ∀ i,(q:ℝ)<(Z i).target) (ω : Ω) :
    current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q ω=
      NativeJointHistory.evaluate 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z ω (q:ℝ) := by
  rw [current_eq_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q hgap ω]
  exact (NativeJointHistory.evaluate_eq_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q q hgap le_rfl ω).symm

include hIJ₀ hIJ₁ in
/-- The original joint stopped flow has the exact printed profile mean
at every NATIVE leaf. Its current displacement fractional moments are
proved from the same full-horizon BDG input. Root stops may differ from
root targets; positive-epsilon non-native leaves are not identified here. -/
theorem native_leaf_fractional_moment (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hΛ : 0≤Λ) (hgap : ∀ i,(q:ℝ)<(Z i).target) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (i : Fin n) (hnative : (Z i).stop=(Z i).target)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    let ref := ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (1,((Z i).target,(Z i).center))
    let Y := fun ω => current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q ω i-ref
    Integrable (fun ω => |Y ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|Y ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  intro ref Y
  have hstop : (q:ℝ)≤(Z i).stop := by rw [hnative];exact (hgap i).le
  have hh := NativeJointMoments.fractional_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    Z q q hΛ hgap le_rfl hqH hq1 i hstop p B hBDG hβ hβ1
  have hinit : NativeJointObservations.initial Λ u₀ v₀ Z i=ref := by
    rw [NativeJointObservations.initial_physical_mean Λ u₀ v₀ Z (fun j => q.2.trans_lt (hgap j)) i,hnative]
    simp only [ref,ControlledProfile.mean,one_mul]
  have he (ω : Ω) : Y ω=NativeJointMoments.displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q q i ω := by
    dsimp only [Y]
    rw [current_eq_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q hgap ω]
    exact congrArg (fun z => NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z q q ω i-z) hinit.symm
  simp_rw [he]
  exact hh

end SHE.NativeJointMeanDisplacement

namespace SHE.MixedNativeJointMeanDisplacement
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance jointMeanDisplacementLocal8 : Fact (0<2*π) := ⟨by positivity⟩
local instance jointMeanDisplacementLocal9 : MeasurableSpace RealL2 := borel _
local instance jointMeanDisplacementLocal10 : BorelSpace RealL2 := ⟨rfl⟩
local instance jointMeanDisplacementLocal11 : MeasurableSpace RealHaarInput := borel _
local instance jointMeanDisplacementLocal12 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointMeanDisplacementLocal13 : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointMeanDisplacementLocal14 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def current (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) (ω : Ω) : GaussianIncrement.State n :=
  WithLp.toLp 2 (fun i => functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
    Real.exp (-Λ*((Z i).stop-(q:ℝ)))*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω))

theorem current_measurable (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) :
    Measurable (current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  simp_rw [map_sub]
  exact ((functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hU).add
    ((((functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hV).sub
      ((functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hU)).const_mul _)

theorem current_eq_value (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hgap : ∀ i,(q:ℝ)<(Z i).target) (ω : Ω) :
    current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q ω=
      MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q q ω := by
  apply PiLp.ext
  intro i
  exact (MixedNativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q hgap q le_rfl ω i).symm

theorem current_eq_evaluate (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hgap : ∀ i,(q:ℝ)<(Z i).target) (ω : Ω) :
    current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q ω=
      MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z ω (q:ℝ) := by
  rw [current_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q hgap ω]
  exact (MixedNativeJointHistory.evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q q hgap le_rfl ω).symm

include hIJ₀ hIJ₁ in
/-- The original joint stopped flow has the exact printed profile mean
at every NATIVE leaf. Its current displacement fractional moments are
proved from the same full-horizon BDG input. Root stops may differ from
root targets; positive-epsilon non-native leaves are not identified here. -/
theorem native_leaf_fractional_moment (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hΛ : 0≤Λ) (hgap : ∀ i,(q:ℝ)<(Z i).target) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (i : Fin n) (hnative : (Z i).stop=(Z i).target)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    let ref := ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (1,((Z i).target,(Z i).center))
    let Y := fun ω => current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q ω i-ref
    Integrable (fun ω => |Y ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|Y ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  intro ref Y
  have hstop : (q:ℝ)≤(Z i).stop := by rw [hnative];exact (hgap i).le
  have hh := MixedNativeJointMoments.fractional_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    Z q q hΛ hgap le_rfl hqH hq1 i hstop p B hBDG hβ hβ1
  have hinit : MixedNativeJointObservations.initial Λ u₀ v₀ Z i=ref := by
    rw [MixedNativeJointObservations.initial_apply,hnative,functional_physical (q.2.trans_lt (hgap i)),functional_physical (q.2.trans_lt (hgap i))]
    simp only [ref,ControlledProfile.mean,one_mul]
  have he (ω : Ω) : Y ω=MixedNativeJointMoments.displacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q q i ω := by
    dsimp only [Y]
    rw [current_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q hgap ω]
    exact congrArg (fun z => MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q q ω i-z) hinit.symm
  simp_rw [he]
  exact hh

end SHE.MixedNativeJointMeanDisplacement
