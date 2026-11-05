module

public import SHE.JointInterpolationAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section

namespace SHE.MixedJointInterpolationMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance mixedJointInterpolation_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
local instance mixedJointInterpolation_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedJointInterpolation_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedJointInterpolation_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedJointInterpolation_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedJointInterpolation_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedJointInterpolation_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

def mean (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) (θ : ℝ) (ω : Ω) : WordRecursion.State n :=
  JointInterpolationAlgebra.current Λ q θ (S.first q ω) (S.second q ω) Z

theorem mean_joint_measurable (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) :
    Measurable (fun z : ℝ×Ω=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q z.1 z.2) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hFU := (functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hU
  have hFV := (functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hV
  change Measurable (fun z : ℝ×Ω=>functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q z.2)+
    z.1*exp (-Λ*((Z i).stop-(q:ℝ)))*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q z.2-S.first q z.2))
  simp_rw [map_sub]
  exact (hFU.comp measurable_snd).add
    ((measurable_fst.mul_const _).mul ((hFV.sub hFU).comp measurable_snd))

theorem mean_measurable (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0) (θ : ℝ) :
    Measurable (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q θ) := by
  have hU : Measurable (S.first q) :=
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  have hV : Measurable (S.second q) :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hFU := (functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hU
  have hFV := (functional ((Z i).target-(q:ℝ)) (Z i).center).continuous.measurable.comp hV
  change Measurable (fun ω=>functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
    θ*exp (-Λ*((Z i).stop-(q:ℝ)))*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω))
  simp_rw [map_sub]
  exact hFU.add ((hFV.sub hFU).const_mul _)

include hIJ₀ hIJ₁ in
/-- Literal controlled JOINT interpolation offsets for every |theta|≤1.
At each native leaf sigma=target, the extra theta-damping is retained
inside the same full-H hybrid input. The reference mean is the complete
theta-profile mean, not either endpoint or a compensated-future mean. -/
theorem native_leaf_fractional_moment (Z : Fin n→WordRecursion.Observation) (q : ℝ≥0)
    (hΛ : 0≤Λ) (hgap : ∀ i,(q:ℝ)<(Z i).target) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {θ : ℝ} (hθ : |θ|≤1) (i : Fin n) (hnative : (Z i).stop=(Z i).target)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    let Y := fun ω=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z q θ ω i-
      ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (θ,((Z i).target,(Z i).center))
    Integrable (fun ω=>|Y ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|Y ω|^(((2*p:ℕ):ℝ)*β) ∂μ)≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  intro Y
  let amp := θ*exp (-Λ*((Z i).target-(q:ℝ)))
  have hamp : |amp|≤1 := JointInterpolationAlgebra.damped_parameter_bound hΛ (hgap i).le hθ
  have hy := MixedNativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH (hgap i) (Z i).center hamp
  have hh := NativeHybridMoments.fractional_moment 𝓕 μ H hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbU 0).1.trans (hbU 0).2))
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first)
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second)
    S.first_coefficient S.second_coefficient q (hgap i) (Z i).center hΛ hamp J hqH hq1 p B hBDG hβ hβ1
  have he : (fun ω=>|Y ω|^(((2*p:ℕ):ℝ)*β))=ᵐ[μ]
      fun ω=>|J.integral (MixedNativePairHybridIdentity.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S q (hgap i) (Z i).center hΛ hamp) ω|^(((2*p:ℕ):ℝ)*β) := by
    filter_upwards [hy] with ω hω
    apply congrArg (fun z : ℝ=>|z|^(((2*p:ℕ):ℝ)*β))
    change functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
      θ*exp (-Λ*((Z i).stop-(q:ℝ)))*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω)-
        ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (θ,((Z i).target,(Z i).center))=_
    rw [hnative]
    exact (JointInterpolationAlgebra.centered_native_eq_hybrid Λ θ q (hgap i) (Z i).center
      (S.first q ω) (S.second q ω) u₀ v₀).trans hω
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans_le hh.2⟩

end SHE.MixedJointInterpolationMoments
