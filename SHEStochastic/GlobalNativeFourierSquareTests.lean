module

public import SHEStochastic.GlobalBoundedFourierMartingale

public import SHEStochastic.NativeFourierSquareTests

public import SHEStochastic.CanonicalFourierCompensator
public import SHEStochastic.CanonicalLawMartingaleTests
public import SHEStochastic.WeakLimitCompensatedProducts
public import SHEStochastic.NativeHorizonRestriction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalNativeFourierSquareTests
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation
open SHE.FiniteHaar AddCircle UnboundedNativeHeatEquation
open scoped NNReal ENNReal
open scoped Topology

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

open NativeFourierSquareTests

/-- All square-compensator past-test identities hold on each actual
approximation law, with its literal coefficient covariance. -/
theorem identity (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (hInitial : W 0 =ᵐ[μ] ξ)
    (hEquation : UnboundedGlobalNativeEquation.RandomEquation F μ H W hW hG hβ hβ1 P e ξ)
    (K : ℝ≥0) (hK : K ≤ H) (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction (CanonicalFourierFluctuation.Space (ι := ι) K) ℝ) :
    (∫ x, ψ (CanonicalStateDriverFiltration.history K s x) *
      (WeakLimitCompensatedProducts.value (CanonicalFourierFluctuation.value K a n)
        (CanonicalFourierFluctuation.value K a n) (compensator hG hβ hβ1 B hb a n K) t x -
       WeakLimitCompensatedProducts.value (CanonicalFourierFluctuation.value K a n)
        (CanonicalFourierFluctuation.value K a n) (compensator hG hβ hβ1 B hb a n K) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ K
        (NativeHorizonRestriction.family P K hK) W hcW)) = 0 := by
  letI : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
  letI : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  let R := NativeHorizonRestriction.family P K hK
  let X := CanonicalNativeBrownian.bundle F μ K R W hcW
  let r := BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n
  let M := CanonicalFourierFluctuation.value (ι := ι) K a n
  let A := compensator (ι := ι) hG hβ hβ1 B hb a n K
  have hWa (t : ℝ≥0) : Measurable[F t] (W t) :=
    ((show IsStronglyPredictable F W from hW).stronglyAdapted t).measurable
  obtain ⟨N, _, haN, _, _, hrN, heN⟩ := GlobalBoundedFourierMartingale.exists_version
    F μ H W hW hG hβ hβ1 B hb P e ξ a n hH hcW hnull hEquation
  have hSq := PredictableBracket.square_compensator_martingale
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) (FiniteCylindricalIto.pastLocality P e)
    r haN hrN
  apply CanonicalLawMartingaleTests.identity μ F K X
    (CanonicalNativeBrownian.measurable_bundle F μ K R W hcW hWa)
    (CanonicalStateDriverFiltration.history K) (WeakLimitCanonicalBrownian.continuous_history K)
    (CanonicalNativeBrownian.past_adapted_capped F μ K R W hcW hWa)
    (WeakLimitCompensatedProducts.value M M A)
    (fun u ↦ ((CanonicalFourierFluctuation.continuous K a n u).mul
      (CanonicalFourierFluctuation.continuous K a n u)).sub (A u).continuous)
    (fun u sample ↦ N u sample^2-PredictableBracket.energy r u sample) hSq
  · intro u
    filter_upwards [CanonicalFourierFluctuation.comp_bundle K a n F μ R W hcW ξ hInitial u,
      heN, NativeFourierCompensatorValue.energy_ae hG hβ hβ1 B hb a n F μ H W hW]
      with sample hu he henergy
    dsimp only [Function.comp_apply] at hu ⊢
    change M u (X sample)*M u (X sample)-
      CanonicalFourierCompensator.value K (2*(n : ℝ)^2) _ _ u (X sample) = _
    simp only [M, X, r] at hu ⊢
    rw [hu, he (min u K) ((min_le_right _ _).trans hK),
      CanonicalFourierCompensator.comp_bundle,
      ← henergy (min u K) ((min_le_right _ _).trans hK), pow_two]
  · exact hst

end SHEStochastic.GlobalNativeFourierSquareTests
