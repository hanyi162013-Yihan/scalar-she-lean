module

public import SHEStochastic.GlobalNativeRandomInitialKernel
public import SHEStochastic.ScalarVarianceNormalization
public import SHEStochastic.GlobalNativeContinuationKernel
public import SHEStochastic.NativeContinuationCharacteristics
public import SHEStochastic.GlobalCanonicalMildFourierCharacteristics
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalScalarVarianceNormalization
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open GaussianItoTest JointFourierCylinderGenerator
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

open ScalarVarianceNormalization
variable {G : ℝ → ℝ} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β)

/-- Construct continuation for a bounded nondegenerate scalar
coefficient of either sign, using smooth approximations of its variance.
The sign is absorbed into a fixed spatial noise basis. -/
theorem exists_kernel {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (P : FiniteScalarIto.Family F μ H ι) (q : HilbertBasis ι ℝ Noise)
    (hβlt : β < 1) (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)
    (ell : ℝ) (hell : 0 < ell) (helliptic : ∀ z, ell ≤ (G z)^2)
    (hH : 0 < H)
    (ρ : Measure RealL2) [IsProbabilityMeasure ρ] (hρ : MemLp (id : RealL2 → RealL2) 2 ρ) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H),
      CanonicalInitialKernel.initialLaw H Q.toMeasure = ρ ∧
      NativeContinuationCharacteristics.BrownianInput H Q.toMeasure ∧
      ∀ᵐ u ∂ρ,
        CanonicalMildFourierCharacteristics.Holds H (CanonicalInitialKernel.kernel H Q.toMeasure u)
          hG hβ hβlt B hb q ∧ ∀ v : ι → ℝ,
        (∀ᵐ y ∂NativeContinuationKernel.joint H Q.toMeasure (u,v),
          y (StoppedPathPasting.origin H) = (u,v)) ∧
        JointFourierProblem.Holds hG hβ hβlt.le B B.property hb H q
          (NativeContinuationKernel.joint H Q.toMeasure (u,v)) := by
  have hv := square_holder hG B hb
  have hbounds (z : ℝ) : ell ≤ (G z)^2 ∧ (G z)^2 ≤ (B : ℝ)^2 := by
    refine ⟨helliptic z, ?_⟩
    have hz : |G z| ≤ B := by simpa only [Real.norm_eq_abs] using hb z
    nlinarith [sq_abs (G z), abs_nonneg (G z), B.property]
  have hne (z : ℝ) : G z ≠ 0 := by
    intro hz
    have h := helliptic z
    rw [hz] at h
    nlinarith
  obtain ⟨σ, hσ, he⟩ : ∃ σ : ℝ, σ^2 = 1 ∧
      ∀ z, PositiveScalarApproximation.root (a := fun z ↦ (G z)^2) z = σ*G z := by
    rcases constant_sign (hG.continuous hβ) hne with hp | hn
    · refine ⟨1, by norm_num, ?_⟩
      intro z
      simp [PositiveScalarApproximation.root, Real.sqrt_sq (hp z).le]
    · refine ⟨-1, by norm_num, ?_⟩
      intro z
      simp [PositiveScalarApproximation.root, Real.sqrt_sq_eq_abs, abs_of_neg (hn z)]
  let r := signBasis q σ hσ
  let hr := PositiveScalarApproximation.root_holder hv hβ ell ((B : ℝ)^2) hell hbounds
  let A := PositiveScalarApproximation.bound ((B : ℝ)^2)
  let hbRoot := PositiveScalarApproximation.root_bound ell ((B : ℝ)^2) hbounds
  have hA : A = B := NNReal.eq (Real.sqrt_sq B.property)
  have hbRootB : ∀ z, ‖PositiveScalarApproximation.root (a := fun z ↦ (G z)^2) z‖ ≤ B := by
    intro z
    have hz : ‖PositiveScalarApproximation.root (a := fun z ↦ (G z)^2) z‖ ≤ A := hbRoot z
    rw [hA] at hz
    exact hz
  obtain ⟨Q, hQ, hs⟩ := GlobalNativeRandomInitialKernel.exists_kernel F μ H P r hv hβ hβlt
    ell ((B : ℝ)^2) hell hbounds hH ρ hρ
  refine ⟨Q, hQ, hs.mono (fun _ hu ↦ hu.choose), ?_⟩
  have hp := GlobalNativeContinuationKernel.properties H Q.toMeasure hr hβ hβlt A hbRoot r hH hs
  rw [hQ] at hp
  have hSupport := hs
  unfold GlobalNativeFourierLimitKernel.Supports at hSupport
  rw [hQ] at hSupport
  filter_upwards [hp, hSupport] with u hu hsu
  obtain ⟨hBrown, hMild⟩ := hsu
  have hRoot := GlobalCanonicalMildFourierCharacteristics.holds H (CanonicalInitialKernel.kernel H Q.toMeasure u)
    hr hβ hβlt A hbRoot r hBrown hH hMild
  have hRootB : CanonicalMildFourierCharacteristics.Holds H (CanonicalInitialKernel.kernel H Q.toMeasure u)
      hr hβ hβlt B hbRootB r := by simpa only [hA] using hRoot
  refine ⟨fourier_holds hG hr hβ σ hσ he hβlt B hb hbRootB q r
    (signBasis_apply q σ hσ) H _ hRootB, ?_⟩
  intro v
  refine ⟨(hu v).1, ?_⟩
  intro s d a n driver f hf hSmooth hs
  exact problem hG hr hβ hβlt.le σ hσ he B A B.property A.property hb hbRoot q r
    (signBasis_apply q σ hσ) H _ (hu v).2 a n driver f hf hSmooth hs

end SHEStochastic.GlobalScalarVarianceNormalization
