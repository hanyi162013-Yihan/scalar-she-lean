module

public import SHE.MixedNativePairMartingale
public import SHE.NativeJointObservations
public import SHE.NativeJointIto
public import SHE.NativeJointBackwardStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeJointObservations
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance nativeJointObservations_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointObservations_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointObservations_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointObservations_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointObservations_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointObservations_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {n : ℕ}

def weights (Λ : ℝ) (Z : Fin n→WordRecursion.Observation) : Fin n→ℝ :=
  fun i => Real.exp (-Λ*(Z i).stop)

def initial (Λ : ℝ) (u₀ v₀ : RealL2) (Z : Fin n→WordRecursion.Observation) : State n :=
  FiniteItoBlockMap.blockMap (weights Λ Z)
    (MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i => (Z i).target) (fun i => (Z i).center))

@[simp] theorem initial_apply (Λ : ℝ) (u₀ v₀ : RealL2) (Z : Fin n→WordRecursion.Observation) (i : Fin n) :
    initial Λ u₀ v₀ Z i=functional (Z i).target (Z i).center u₀+
      Real.exp (-Λ*(Z i).stop)*functional (Z i).target (Z i).center (v₀-u₀) := by
  simp only [initial,FiniteItoBlockMap.blockMap_apply,MixedNativePairExtendedMartingale.initial,
    WithLp.ofLp_toLp,Fin.append_left,Fin.append_right,weights]

theorem initial_physical_mean (Λ : ℝ) (u₀ v₀ : RealL2) (Z : Fin n→WordRecursion.Observation)
    (hT : ∀ i,0<(Z i).target) (i : Fin n) :
    initial Λ u₀ v₀ Z i=PhysicalProfile.physicalHeatMean (embed u₀) ((Z i).target,(Z i).center)+
      Real.exp (-Λ*(Z i).stop)*PhysicalProfile.physicalHeatMean (embed (v₀-u₀)) ((Z i).target,(Z i).center) := by
  rw [initial_apply,functional_physical (hT i),functional_physical (hT i)]

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
variable (Z : Fin n→WordRecursion.Observation) (b : ℝ≥0)
variable (hgap : ∀ i,(b:ℝ)<(Z i).target)

/-- The printed drift-cancelling joint observations are aU constant
linear image of the genuine extended observation martingale. Each
original stop remains separate from its heat target. -/
def value (t : ℝ≥0) (ω : Ω) : State n :=
  FiniteItoBlockMap.blockMap (weights Λ Z)
    (MixedNativePairExtendedMartingale.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b t ω)

def rows (hΛ : 0≤Λ) : Fin n→Process (E := Both RealHaarInput) 𝓕 μ H :=
  FiniteItoBlockMap.rows 𝓕 μ H (weights Λ Z)
    (MixedNativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ)

theorem continuous_value (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b t ω) :=
  (FiniteItoBlockMap.blockMap (weights Λ Z)).continuous.comp
    (MixedNativePairExtendedMartingale.continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b ω)

include hgap in
theorem value_eq_physical (q : ℝ≥0) (hqb : q≤b) (ω : Ω) (i : Fin n) :
    value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q ω i=
      functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
        Real.exp (-Λ*((Z i).stop-(q:ℝ)))*
          functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω) := by
  rw [value,FiniteItoBlockMap.blockMap_apply]
  simp only [MixedNativePairExtendedMartingale.value,WithLp.ofLp_toLp,Fin.append_left,Fin.append_right,
    MixedNativePairLocalMartingale.value,min_eq_left hqb,weights]
  have hage : (Z i).target-(b:ℝ)≤(Z i).target-(q:ℝ) := sub_le_sub_left (by exact_mod_cast hqb) _
  rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _ hage,
    PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _ hage,← map_sub]
  dsimp only [Function.uncurry]
  have he : Real.exp (-Λ*(Z i).stop)*Real.exp (Λ*(q:ℝ))=Real.exp (-Λ*((Z i).stop-(q:ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc,he]

include hgap in
theorem value_at_original_stop (q : ℝ≥0) (hqb : q≤b) (ω : Ω) (i : Fin n) (hstop : (Z i).stop=(q:ℝ)) :
    value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b q ω i=
      functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω) := by
  rw [value_eq_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap q hqb ω i,hstop,
    sub_self,mul_zero,Real.exp_zero,one_mul,map_sub]
  ring

include hIJ₀ hIJ₁ in
theorem integral_representation (hΛ : 0≤Λ) (hbH : b≤H) (t : ℝ≥0) :
    value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b t=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (initial Λ u₀ v₀ Z)
        (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ) t := by
  have he := MixedNativePairExtendedMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ hbH t
  have hm := FiniteItoBlockMap.vectorIntegral_map 𝓕 μ H J (weights Λ Z)
    (MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i => (Z i).target) (fun i => (Z i).center))
    (MixedNativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ) t
  filter_upwards [he,hm] with ω he hm
  change FiniteItoBlockMap.blockMap (weights Λ Z) _=_
  rw [he]
  exact hm

include hIJ₀ hIJ₁ hgap in
theorem predictable_value (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hΛ : 0≤Λ) (hbH : b≤H) :
    StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)) :=
  (FiniteItoBlockMap.blockMap (weights Λ Z)).continuous.comp_stronglyMeasurable
    (MixedNativePairExtendedMartingale.predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hnull hΛ hbH)

end SHE.MixedNativeJointObservations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000

namespace SHE.MixedNativeJointIto
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open MixedNativeJointObservations
open scoped NNReal ENNReal
local instance nativeJointIto_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
/-- Ordinary finite-dimensional Itô applies directly to the actual
drift-cancelling joint observations, with their original separate stops
and targets. No additional formula or applicability assumption is used. -/
theorem finiteItoInput (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(Z i).target) (hbH : b≤H)
    {s : ℝ} (hs : 0≤s) (hsb : s≤(b:ℝ)) :
    ∃ N : (ℝ→WordRecursion.State n→ℝ)→Ω→ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω t => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b t.toNNReal ω)
        (StandardFiniteIto.rowCovariance 𝓕 μ H
          (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ)) s b N := by
  let Y := Function.uncurry (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
  let R := rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ
  have hY : StronglyMeasurable[𝓕.predictable] Y := predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH
  let N : (ℝ→WordRecursion.State n→ℝ)→Ω→ℝ := fun G ω =>
    FiniteItoNoise.noise 𝓕 μ H Y hY R J s b G ω
  refine ⟨N,fun G => ⟨FiniteItoNoise.noise_integrable 𝓕 μ H Y hY R J s b G,
    FiniteItoNoise.noise_centered 𝓕 μ H Y hY R J s b G⟩,?_⟩
  exact StandardFiniteIto.finiteItoInput 𝓕 μ H J hJ R (initial Λ u₀ v₀ Z) Y hY
    (continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
    (fun t _ => integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      Z b hgap hΛ hbH t) hs hsb (by exact_mod_cast hbH)

end SHE.MixedNativeJointIto

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedNativeJointBackwardStep
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianItoTest GaussianTaylor GaussianTaylorAverage CovarianceEndpoint
open scoped NNReal ENNReal
local instance nativeJointBackwardStep_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointBackwardStep_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointBackwardStep_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointBackwardStep_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointBackwardStep_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointBackwardStep_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

theorem cancellation {n : ℕ} (W : EndpointWindow n) (F : State n→ℝ)
    (Γ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (z : State n) :
    backwardDerivative W F t z+(1/2:ℝ)*covarianceAction Γ (hessian (backward W F t) z)=
      (1/2:ℝ)*covarianceAction (Γ-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
        (hessian (backward W F t) z) := by
  rw [NativeControlledGenerator.covarianceAction_sub]
  unfold backwardDerivative
  ring

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
/-- Actual drift-free joint backward step before the original stops.
Its only stochastic formula assumption is the original universal Itô
package. Singular Gaussian covariance and colliding observations are
allowed; the reference PDE and its cancellation are proved. -/
theorem one_step (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    {n : ℕ} (W : EndpointWindow n) (hleft : 0≤W.left)
    (b : ℝ≥0) (hW : W.right=(b:ℝ)) (hbH : b≤H)
    (hgap : ∀ i,(b:ℝ)<(W.observations i).target)
    (_hstop : ∀ i,(b:ℝ)≤(W.observations i).stop)
    {F : State n→ℝ} (hF : BoundedSmooth F) :
    let Y := fun (ω : Ω) (t : ℝ) => MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      W.observations b t.toNNReal ω
    let R := MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W.observations b hgap hΛ
    ∃ N : Ω→ℝ,Integrable N μ ∧ (∫ ω,N ω ∂μ)=0 ∧ ∀ᵐ ω ∂μ,
      F (Y ω b)=WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F (Y ω W.left)+N ω+
        ∫ t in W.left..W.right,(1/2:ℝ)*covarianceAction
          (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
          (hessian (backward W F t) (Y ω t)) := by
  intro Y R
  obtain ⟨N,hNc,hIto⟩ := MixedNativeJointIto.finiteItoInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hnull hJ hΛ W.observations b hgap hbH hleft (by simpa only [hW] using W.ordered)
  have hIto' : PhysicalIto.FiniteItoInput μ Y (StandardFiniteIto.rowCovariance 𝓕 μ H R)
      W.left W.right N := by rw [hW];exact hIto
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  obtain ⟨K,hK,hHK⟩ := hF.hessian_lipschitz
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  have hr := backward_regular W (hF.smooth.of_le (by simp)) hM hA hB hB0 hK hHK
  refine ⟨N (backward W F),(hNc _).1,(hNc _).2,?_⟩
  filter_upwards [hIto' _ _ hr] with ω hω
  rw [PhysicalIto.backward_terminal W F,
    PhysicalIto.backward_eq_semigroup W F ⟨le_rfl,W.ordered⟩] at hω
  have htime : Y ω W.right=Y ω (b:ℝ) := congrArg (Y ω) hW
  rw [htime] at hω
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact cancellation W F _ t _

end SHE.MixedNativeJointBackwardStep
