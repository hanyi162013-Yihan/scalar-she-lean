module

public import SHE.NativePairHybridIdentity
public import SHE.ControlledFutureMeans

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativePairFutureMean
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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
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
        J.integral (NativePairHybridIdentity.input 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
          q (hgap i) (nativeCenter centers i) hΛ hθ) ω := by
  have hh (i : Fin n) := NativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ ha hell hb
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

end SHE.NativePairFutureMean
