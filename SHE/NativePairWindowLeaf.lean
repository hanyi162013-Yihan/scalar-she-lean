module

public import SHE.NativePairFutureMoments
public import SHE.ControlledFutureFields
public import SHE.ControlledWindowOffsetLeaf

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativePairWindowLeaf
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
open scoped NNReal ENNReal BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)

def futureMean (q : ℝ≥0) {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (θ : ℝ) (ω : Ω) : State n :=
  futureMeanVector Λ target centers q q.2 (embed u₀) (embed (v₀-u₀))
    (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ

omit [IsProbabilityMeasure μ] in
theorem futureMean_measurable (q : ℝ≥0) {n : ℕ} (target : Fin n→ℝ)
    (centers : Fin n→UnitAddCircle) (hgap : ∀ i,(q:ℝ)<target i) (θ : ℝ) :
    Measurable (futureMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ) := by
  have hU : Measurable (fun ω => embed (S.first q ω)) :=
    embed.continuous.measurable.comp (((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id))
  have hV : Measurable (fun ω => embed (S.second q ω)) :=
    embed.continuous.measurable.comp (((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id))
  have hD : Measurable (fun ω => embed (S.second q ω-S.first q ω)) := by
    have he : (fun ω => embed (S.second q ω-S.first q ω))=
        ((fun ω => embed (S.second q ω))-(fun ω => embed (S.first q ω))) := by
      funext ω
      exact map_sub embed _ _
    rw [he]
    exact hV.sub hU
  exact ControlledFutureFields.futureMeanVector_measurable Λ (fun _ => target) (fun _ => measurable_const)
    (fun _ => centers) (fun _ => measurable_const) (fun _ => (q:ℝ)) measurable_const (fun _ => q.2)
    (fun _ => hgap) (fun _ => embed u₀) (fun _ => embed (v₀-u₀))
    _ _ measurable_const hU hD (fun _ => θ) measurable_const

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- An actual native current-state unassigned rough leaf, with every old
suppression and the full printed profile baseline retained. All moment
inputs are discharged by the same full-horizon BDG and actual pair
identity. No compatibility of the random current mean is assumed. -/
theorem even_moment (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {n r : ℕ} (σ target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hages : ∀ i,σ i≤target i) (hgap : ∀ i,(q:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)≤lo j)
    (hdisjoint : ∀ j k,j≠k → hi j≤lo k ∨ hi k≤lo j)
    {θ : ℝ} (hθ : |θ|≤1) (i : Fin n) (hnative : σ i=target i)
    (ht : target i∈Ioc 0 P.horizon) (is : List (Fin r)) (p : ℕ) (B0 : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p J B0) :
    let u := embed u₀
    let d := embed (v₀-u₀)
    let center := nativeCenter centers
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center q θ
    let ν := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let m := futureMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ
    let F := fun z : Ω×((Fin r→State n)×State n) =>
      P.coefficient (m z.1 i+((∑ j,suppress is z.2.1 j)+z.2.2) i)-
        ControlledProfile.profile P Λ u d (θ,(target i,center i))
    Integrable (fun z => |F z|^(2*p)) (μ.prod ν) ∧
      (∫ z,|F z|^(2*p) ∂μ.prod ν) ≤ (2 : ℝ)^(2*p-1)*
        (P.holder^(2*p)*(NativeHybridMoments.momentConstant p B0 κ M)^P.exponent*
          (q:ℝ)^((p:ℝ)*P.exponent/2)+
        GaussianCenteredLeafMoments.leafMomentConstant p P.exponent*
          (P.holder*(ProfileVariance.upperConstant*P.upper)^(P.exponent/2)*
            (target i)^(P.exponent/4))^(2*p)) := by
  intro u d center A B ν m F
  let ref := ControlledProfile.mean Λ u d (θ,(target i,center i))
  have hmoment := NativePairFutureMoments.fractional_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hq1 target centers hgap hθ i p B0 hBDG P.exponent_pos.le P.exponent_le_one
  change Integrable (fun ω => |m ω i-ref|^(((2*p:ℕ):ℝ)*P.exponent)) μ ∧ _ at hmoment
  have hiOffset := (measurePreserving_fst (μ:=μ) (ν:=ν)).integrable_comp_of_integrable hmoment.1
  have heOffset : (∫ z : Ω×((Fin r→State n)×State n),
      |m z.1 i-ref|^(((2*p:ℕ):ℝ)*P.exponent) ∂μ.prod ν)=
      ∫ ω,|m ω i-ref|^(((2*p:ℕ):ℝ)*P.exponent) ∂μ := by
    calc
      _=∫ ω,∫ _ : (Fin r→State n)×State n,
          |m ω i-ref|^(((2*p:ℕ):ℝ)*P.exponent) ∂ν ∂μ := by
        convert! integral_prod _ hiOffset using 1
      _=_ := by simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hm : Measurable (fun ω => m ω i) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable.comp
      (futureMean_measurable 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers hgap θ)
  have hh := ControlledWindowOffsetLeaf.even_moment μ P Λ u d θ lo hi hdisjoint
    σ target center hages q.2 hlo i hnative ht is (fun z => m z.1 i)
    (hm.comp measurable_fst) p hiOffset
  refine ⟨hh.1,hh.2.trans ?_⟩
  change (2 : ℝ)^(2*p-1)*(P.holder^(2*p)*
    (∫ z : Ω×((Fin r→State n)×State n),|m z.1 i-ref|^(((2*p:ℕ):ℝ)*P.exponent) ∂μ.prod ν)+
    GaussianCenteredLeafMoments.leafMomentConstant p P.exponent*
      (P.holder*(ProfileVariance.upperConstant*P.upper)^(P.exponent/2)*
        (target i)^(P.exponent/4))^(2*p))≤_
  rw [heOffset]
  have hc := mul_le_mul_of_nonneg_left hmoment.2 (pow_nonneg P.holder_nonneg (2*p))
  convert! mul_le_mul_of_nonneg_left (add_le_add hc le_rfl)
    (show 0≤(2:ℝ)^(2*p-1) by positivity) using 1
  ring

end SHE.NativePairWindowLeaf
