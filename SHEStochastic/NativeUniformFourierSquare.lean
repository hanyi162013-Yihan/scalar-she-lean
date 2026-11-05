module

public import SHEStochastic.NativeUniformFourierIntegral
public import SHEStochastic.PastedHeatProductFunctional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativeUniformFourierSquare
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting
open UnboundedJointCanonicalPathMartingale PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)



local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩



def density (R : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    BoundedContinuousFunction (JointStateDriverPath.State RealL2 ι) ℝ :=
  (NativeFourierCompensatorValue.diagonal (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
    (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) a n).compContinuous ⟨Prod.fst, continuous_fst⟩

theorem compensator_eq (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction RealL2 ℝ)
    (ω : Ω) (t : Time (min H 1)) :
    PastedHeatCovariance.value (min H 1) rate hrate (b.compContinuous ⟨Prod.fst, continuous_fst⟩)
      (path F μ H W P hcW ω) t = ∫ s in 0..t.val, Real.exp (rate*s)*b (W s.toNNReal ω) := by
  rw [PastedHeatCovariance.value_eq]
  apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
  intro s hs
  dsimp only
  rw [show PastedGeneratorFunctional.read (min H 1) (path F μ H W P hcW ω) s =
      UnboundedJointCylinderIdentification.joint F μ H W P s.toNNReal ω from
    NativePathGeneratorFunctional.read_eq (min H 1) _
      (UnboundedJointCylinderIdentification.continuous_joint F μ H W P hcW) ω s
      ⟨hs.1.le, hs.2.le.trans t.property.2⟩]
  rfl

include hH hnull hEquation hM hu₀ in
/-- The source's actual stopped square characteristic is a martingale,
with the bounded cutoff covariance and no new moment premise. -/
theorem martingale (R : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (fun q ω ↦ PastedHeatProductFunctional.value (min H 1) (row (ι := ι) a n) (row a n)
      ((n : ℝ)^2) ((n : ℝ)^2) (by positivity) (density (ι := ι) hG hβ hβ1 R a n)
      (path F μ H W P hcW ω)
      (pastTime (min H 1) (uniformExit H W hcW R ω) (AdaptedCanonicalPathTests.clock (min H 1) q))) F μ := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let K := min H 1
  let r := BoundedFourierInput.input F μ H W hW (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
    (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
    (UnboundedCoefficientCutoff.bounded hG R) a n
  let τ : Ω → WithTop ℝ≥0 := fun ω ↦ AdaptedCanonicalPathTests.toNN K (uniformExit H W hcW R ω)
  obtain ⟨N, hcN, haN, _, _, hrN, heN⟩ := NativeUniformFourierIntegral.exists_version
    F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R a n
  have hs := PredictableBracket.square_compensator_martingale
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e) r haN hrN
  have hsc : ∀ᵐ ω ∂μ, Continuous (fun q ↦ N q ω^2-PredictableBracket.energy r q ω) := by
    filter_upwards [PredictableBracket.continuous_monotone r] with ω hω
    exact (hcN ω |>.pow 2).sub hω.1
  have hτ := UnboundedNativeUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀
    hH hcW hnull hEquation M hM hu₀ R
  have hstop := StoppedSquareZero.stopped_martingale μ F hnull _ hs hsc τ hτ
  have heq : ∀ᵐ ω ∂μ, ∀ q,
      stoppedProcess (fun q ω ↦ N q ω^2-PredictableBracket.energy r q ω) τ q ω =
      PastedHeatProductFunctional.value K (row (ι := ι) a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
        (by positivity) (density (ι := ι) hG hβ hβ1 R a n) (path F μ H W P hcW ω)
        (pastTime K (uniformExit H W hcW R ω) (AdaptedCanonicalPathTests.clock K q)) := by
    filter_upwards [heN, NativeFourierCompensatorValue.energy_ae
      (UnboundedCoefficientCutoff.holder hG R) hβ hβ1
      (UnboundedJointNativePasting.bound (G := G) (C := C) (β := β) R)
      (UnboundedCoefficientCutoff.bounded hG R) a n F μ H W hW] with ω hn he q
    let t := pastTime K (uniformExit H W hcW R ω) (AdaptedCanonicalPathTests.clock K q)
    have hclock := AdaptedCanonicalPathTests.stopped_clock K (uniformExit H W hcW R ω) q
    have hNN : t.val.toNNReal = AdaptedCanonicalPathTests.toNN K t :=
      NNReal.eq (Real.coe_toNNReal _ t.property.1)
    have hmode := hn q
    change NativeUniformStoppedFourier.coordinate W a n (min (q : WithTop ℝ≥0) (τ ω)).untopA ω =
      N (min (q : WithTop ℝ≥0) (τ ω)).untopA ω at hmode
    rw [hclock] at hmode
    have henergy := he (AdaptedCanonicalPathTests.toNN K t) (t.property.2.trans (min_le_left _ _))
    change stoppedProcess (fun q ω ↦ N q ω^2-PredictableBracket.energy r q ω) τ q ω = _
    simp only [stoppedProcess]
    rw [hclock]
    unfold PastedHeatProductFunctional.value
    rw [NativeUniformFourierPrefix.path_value, hNN, hmode]
    simp only [pow_two]
    congr 1
    rw [henergy, density, compensator_eq]
    apply intervalIntegral.integral_congr
    intro s _
    congr 1
    congr 1
    ring
  exact hstop.congr
    (fun q ↦ NullCompleteFiltration.stronglyMeasurable_congr F μ hnull q (hstop.stronglyAdapted q)
      (heq.mono fun ω hω ↦ (hω q).symm)) (fun q ↦ heq.mono fun ω hω ↦ hω q)

end SHEStochastic.NativeUniformFourierSquare
