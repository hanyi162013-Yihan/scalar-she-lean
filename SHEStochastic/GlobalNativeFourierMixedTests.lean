module

public import SHEStochastic.GlobalBoundedFourierMartingale

public import SHEStochastic.NativeFourierMixedTests

public import SHEStochastic.GlobalNativeFourierSquareTests
public import SHEStochastic.CanonicalBrownianSubGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.GlobalNativeFourierMixedTests
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle UnboundedNativeHeatEquation
open scoped NNReal ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B) (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
  (ξ : Ω → RealL2) (a : ℂ →L[ℝ] ℝ) (n : ℤ)

open NativeFourierMixedTests

/-- The actual Fourier/Brownian mixed compensator supplies canonical
full-history identities, without replacing the given noise. -/
theorem identity (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (hInitial : W 0 =ᵐ[μ] ξ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (K : ℝ≥0) (hK : K ≤ H) (i : ι) (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction (CanonicalFourierFluctuation.Space (ι := ι) K) ℝ) :
    (∫ x, ψ (CanonicalStateDriverFiltration.history K s x)*
      (WeakLimitCompensatedProducts.value (CanonicalFourierFluctuation.value K a n)
        (CanonicalStateDriverFiltration.coordinate K i) (compensator hG hβ hβ1 B hb a n (e i) K) t x -
       WeakLimitCompensatedProducts.value (CanonicalFourierFluctuation.value K a n)
        (CanonicalStateDriverFiltration.coordinate K i) (compensator hG hβ hβ1 B hb a n (e i) K) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ K
        (NativeHorizonRestriction.family P K hK) W hcW)) = 0 := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let R := NativeHorizonRestriction.family P K hK
  let X := CanonicalNativeBrownian.bundle F μ K R W hcW
  let r := BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n
  let v := RotatedCylindricalCoordinates.constant F μ H (e i)
  let M := CanonicalFourierFluctuation.value (ι := ι) K a n
  let D := CanonicalStateDriverFiltration.coordinate (E := RealL2) K i
  let A := compensator (ι := ι) hG hβ hβ1 B hb a n (e i) K
  have hWa (t : ℝ≥0) : Measurable[F t] (W t) :=
    ((show IsStronglyPredictable F W from hW).stronglyAdapted t).measurable
  obtain ⟨N, _, haN, _, _, hrN, heN⟩ := GlobalBoundedFourierMartingale.exists_version
    F μ H W hW hG hβ hβ1 B hb P e ξ a n hH hcW hnull hEquation
  obtain ⟨L, _, haL, _, _, hrL⟩ := NativeMartingaleVersion.exists_version P e hnull v
  have hCross := NativeCrossCompensator.martingale
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    r v N L haN haL hrN hrL
  have hDriver (u : ℝ≥0) : (D u ∘ X) =ᵐ[μ] L (min u K) := by
    filter_upwards [hrL (min u K), FiniteCylindricalIto.coordinate_integral P e i (min u K)
      ((min_le_right _ _).trans hK), FiniteScalarIto.zero_ae P.toCoordinates i]
      with sample hL hcoord h0
    change R.W i (0+(CanonicalStateDriverFiltration.clock K u).val.toNNReal) sample -
      R.W i 0 sample = L (min u K) sample
    rw [CanonicalFourierFluctuation.clock_time K u, zero_add]
    change P.W i (min u K) sample-P.W i 0 sample = _
    rw [h0, sub_zero]
    exact hcoord.symm.trans hL.symm
  apply CanonicalLawMartingaleTests.identity μ F K X
    (CanonicalNativeBrownian.measurable_bundle F μ K R W hcW hWa)
    (CanonicalStateDriverFiltration.history K) (WeakLimitCanonicalBrownian.continuous_history K)
    (CanonicalNativeBrownian.past_adapted_capped F μ K R W hcW hWa)
    (WeakLimitCompensatedProducts.value M D A)
    (fun u ↦ ((CanonicalFourierFluctuation.continuous K a n u).mul
      (WeakLimitCanonicalBrownian.continuous_coordinate K i u)).sub (A u).continuous)
    (fun u sample ↦ N u sample*L u sample-NativeCrossCompensator.value r v u sample) hCross
  · intro u
    filter_upwards [CanonicalFourierFluctuation.comp_bundle K a n F μ R W hcW ξ hInitial u,
      heN, hDriver u, NativeFourierCompensatorValue.mixed_ae hG hβ hβ1 B hb a n F μ H W hW (e i)]
      with sample hu he hd hvalue
    dsimp only [Function.comp_apply] at hu hd ⊢
    change M u (X sample)*D u (X sample)-
      CanonicalFourierCompensator.value K ((n : ℝ)^2) _ _ u (X sample) = _
    rw [hd]
    simp only [M, X, r, v] at hu ⊢
    rw [hu, he (min u K) ((min_le_right _ _).trans hK),
      CanonicalFourierCompensator.comp_bundle,
      ← hvalue (min u K) ((min_le_right _ _).trans hK)]
  · exact hst

end SHEStochastic.GlobalNativeFourierMixedTests
