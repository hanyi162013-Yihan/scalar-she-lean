module

public import SHE.NativeFirstScoreWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.NativeFirstScoreWordMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores
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
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- The genuine random Gaussian-averaged native word has all fixed
moments at the deterministic old-gap/full-age scale. This is the
normalized-amplitude input for good/bad kernel truncation. Its proof
uses the literal current-state BDG moments and Gaussian Jensen; it does
not assume a normalized-kernel estimate or independence from the input. -/
theorem averaged_even_moment (P : CanonicalCovariance.ProfileParameters) (hΛ : 0≤Λ)
    (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    (σ target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (hgap : ∀ i,(q:ℝ)<target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,(q:ℝ)≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l → hi j≤lo l ∨ hi l≤lo j)
    {θ : ℝ} (hθ : |θ|≤1) (second : Fin r→Bool) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target (nativeCenter centers) (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) lo hi j)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (choices : List (Fin r×Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ≠[]→Fin r)
    (hchosen : ∀ j h,chosen j h∈block choices j.succ)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j≤(block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb0 : 0<b) (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0) :
    let u := embed u₀
    let d0 := embed (v₀-u₀)
    let center := nativeCenter centers
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod (multivariateGaussian (0:State n) B)
    let mean := NativePairWindowLeaf.futureMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ
    let W := word P.coefficient second A D choices F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun ω => |∫ x,W (ω,x) ∂νG|^(2*b)) μ ∧
      (∫ ω,|∫ x,W (ω,x) ∂νG|^(2*b) ∂μ)≤constant P r m choices b B0 κ M*
        ((∏ j,scale (second j) (A j) (D j))*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
          ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro u d0 center A B νG mean W
  have hh := joint_even_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P hΛ q hqH hq1
    σ target centers hσ hσ1 hages hgap lo hi hlo hlohi hstop hdisjoint hθ second D hD g leaf hnative ht
    choices hnd chosen hchosen F hFm hA0 hν hf hfb b hb0 B0 hBDG
  have hm : Measurable mean := NativePairWindowLeaf.futureMean_measurable 𝓕 μ H Λ κ hκ ha hell hb
    I₀ I₁ u₀ v₀ S q target centers hgap θ
  have hW : Measurable W := word_measurable P.coefficient P.measurable second A D choices F hFm mean hm g leaf _
  have hi2b : Integrable (fun z => ‖W z‖^(2*b)) (μ.prod νG) := by
    simpa only [Real.norm_eq_abs] using hh.1
  have hi1 := integrable_norm_pow_of_le hW.aestronglyMeasurable (by omega : 1≤2*b) hi2b
  have hiW : Integrable W (μ.prod νG) := (integrable_norm_iff hW.aestronglyMeasurable).mp
    (by simpa only [pow_one] using hi1)
  have hj := UniformFiberMoments.average_even_moment μ νG W hiW b hh.1
  exact ⟨hj.1,hj.2.trans hh.2⟩

end SHE.NativeFirstScoreWordMoments
