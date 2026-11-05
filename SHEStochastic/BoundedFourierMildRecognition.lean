module

public import SHEStochastic.BoundedFourierLift
public import SHEStochastic.NativeFourierStateSeparation
public import SHEStochastic.BoundedHeatTightness
public import SHEStochastic.UnboundedNativeMildRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.BoundedFourierMildRecognition
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation NativeFourierHeatCoordinate
open HeatParameterCover HeatParameterCoordinates HeatParameterPullback
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

def FourierEquation
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ξ : Ω → RealL2) : Prop :=
  ∀ (T : ℝ≥0), T ≤ H → (T : ℝ) ≤ 1 → ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ),
    (fun sample ↦ Real.exp ((T : ℝ)*(n : ℝ)^2)*coordinate a n (W T sample)-coordinate a n (ξ sample)) =ᵐ[μ]
      J.integral (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n))

def BasisFourierEquation
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ξ : Ω → RealL2) : Prop :=
  ∀ (T : ℝ≥0), T ≤ H → (T : ℝ) ≤ 1 → ∀ (a : ℂ →L[ℝ] ℝ),
    a = Complex.reCLM ∨ a = Complex.imCLM → ∀ n : ℤ,
    (fun sample ↦ Real.exp ((T : ℝ)*(n : ℝ)^2)*coordinate a n (W T sample)-coordinate a n (ξ sample)) =ᵐ[μ]
      J.integral (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n))

/-- Native Fourier equations identify a continuous convolution with the
actual L2 state, using only countably many real and imaginary tests. -/
theorem fixed
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ξ : Ω → RealL2) (T : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1)
    (hFourier : ∀ (a : ℂ →L[ℝ] ℝ), a = Complex.reCLM ∨ a = Complex.imCLM → ∀ n : ℤ,
      (fun sample ↦ Real.exp ((T : ℝ)*(n : ℝ)^2)*coordinate a n (W T sample)-coordinate a n (ξ sample)) =ᵐ[μ]
        J.integral (StoppedItoInputs.stop F μ H T (BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n)))
    (Y : Parameter → Ω → ℝ) (hm : ∀ p, Measurable (Y p))
    (hc : ∀ sample, Continuous (fun p ↦ Y p sample))
    (he : ∀ p, Y p =ᵐ[μ] J.integral (BoundedHeatCoefficientLift.input F (physical W)
      (physical_predictable F W hW) hG hβ hβ1.le B hb μ H (time H p)
        (time_le_horizon H p) (time_le_one H p) (center p))) :
    W T =ᵐ[μ] fun sample ↦ NativeHeatObservation.heat T (ξ sample)+
      NativeRemainderObservation.remainder ⟨fun p ↦ Y p sample, hc sample⟩ ⟨T, T.property, hT⟩ := by
  have hh (a : ℂ →L[ℝ] ℝ) (ha : a = Complex.reCLM ∨ a = Complex.imCLM) (n : ℤ) : ∀ᵐ sample ∂μ,
      coordinate a n (W T sample) = coordinate a n (NativeHeatObservation.heat T (ξ sample)+
        NativeRemainderObservation.remainder ⟨fun p ↦ Y p sample, hc sample⟩ ⟨T, T.property, hT⟩) := by
    filter_upwards [hFourier a ha n, BoundedFourierLift.coordinate F μ H W hW hG hβ hβ1 B hb
      J a n T hTH hT Y hm hc he] with sample hf hr
    have hheat := coordinate_heat a n (t := (T : ℝ)) (show 0 ≤ (T : ℝ) from T.2) (ξ sample)
    rw [map_add, hheat, hr]
    simp only [neg_mul]
    have hinv : Real.exp (-((T : ℝ)*(n : ℝ)^2))*Real.exp ((T : ℝ)*(n : ℝ)^2) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have heq := congrArg (fun z : ℝ ↦ Real.exp (-((T : ℝ)*(n : ℝ)^2))*z) hf
    rw [mul_sub, ← mul_assoc, hinv, one_mul] at heq
    linarith
  filter_upwards [ae_all_iff.mpr (hh Complex.reCLM (Or.inl rfl)),
    ae_all_iff.mpr (hh Complex.imCLM (Or.inr rfl))] with sample hre him
  exact NativeFourierStateSeparation.ext hre him

def HasClosedVersion
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ξ : Ω → RealL2) : Prop :=
    ∃ Y : Ω → C(Parameter, ℝ), Measurable Y ∧
      (∀ p, (fun sample ↦ Y sample p) =ᵐ[μ]
        J.integral
          (BoundedHeatCoefficientLift.input F (physical W) (physical_predictable F W hW)
            hG hβ hβ1.le B hb μ H (time H p) (time_le_horizon H p) (time_le_one H p) (center p))) ∧
      ∀ᵐ sample ∂μ, ∀ T : ℝ≥0, T ≤ H → ∀ hT : (T : ℝ) ≤ 1,
        W T sample = NativeHeatObservation.heat T (ξ sample)+
          NativeRemainderObservation.remainder (Y sample) ⟨T, T.property, hT⟩

theorem fourier_of_closed
    (J : StandardTerminalIto (C := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) (E := ℝ) F μ H)
    (ξ : Ω → RealL2) (hMild : HasClosedVersion F μ H W hW hG hβ hβ1 B hb J ξ) :
    FourierEquation F μ H W hW hG hβ hβ1 B hb J ξ := by
  obtain ⟨Y, hm, he, hs⟩ := hMild
  intro T hTH hT a n
  filter_upwards [hs, BoundedFourierLift.coordinate F μ H W hW hG hβ hβ1 B hb
    J a n T hTH hT (fun p sample ↦ Y sample p)
    (fun p ↦ (ContinuousMap.measurable_eval p).comp hm) (fun sample ↦ (Y sample).continuous) he]
    with sample hs hr
  have hh := congrArg (coordinate a n) (hs T hTH hT)
  have hheat := coordinate_heat a n (t := (T : ℝ)) (show 0 ≤ (T : ℝ) from T.2) (ξ sample)
  rw [map_add, hheat] at hh
  have heq := hh.trans (congrArg (fun z : ℝ ↦ Real.exp (-(T : ℝ)*(n : ℝ)^2)*coordinate a n (ξ sample)+z) hr)
  simp only [neg_mul] at heq
  have hinv : Real.exp ((T : ℝ)*(n : ℝ)^2)*Real.exp (-((T : ℝ)*(n : ℝ)^2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hm := congrArg (fun z : ℝ ↦ Real.exp ((T : ℝ)*(n : ℝ)^2)*z) heq
  simp only [mul_add, ← mul_assoc, hinv, one_mul] at hm
  linarith

theorem exists_closed_basis {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (ξ : Ω → RealL2) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hFourier : BasisFourierEquation F μ H W hW hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    HasClosedVersion F μ H W hW hG hβ hβ1 B hb (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ := by
  obtain ⟨Y, hm, he, _⟩ := BoundedHeatTightness.exists_tight_versions F μ H
    (fun _ : ℕ ↦ physical W) (fun _ ↦ physical_predictable F W hW)
    (fun _ ↦ hG) hβ hβ1.le B (fun _ ↦ hb) P e
  refine ⟨Y 0, hm 0, he 0, ?_⟩
  apply UnboundedNativeMildRecognition.close_representation μ H W ξ hH hcW
    (fun p sample ↦ Y 0 sample p) (fun sample ↦ (Y 0 sample).continuous)
  intro T hTH hT
  exact fixed F μ H W hW hG hβ hβ1 B hb (FiniteCylindricalIto.terminalIto P.toCoordinates e)
    ξ T hTH.le hT.le (hFourier T hTH.le hT.le) (fun p sample ↦ Y 0 sample p)
    (fun p ↦ (ContinuousMap.measurable_eval p).comp (hm 0))
    (fun sample ↦ (Y 0 sample).continuous) (he 0)

theorem exists_closed {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (ξ : Ω → RealL2) (hH : 0 < H) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))
    (hFourier : FourierEquation F μ H W hW hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    HasClosedVersion F μ H W hW hG hβ hβ1 B hb (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ :=
  exists_closed_basis F μ H W hW hG hβ hβ1 B hb P e ξ hH hcW
    (fun T hTH hT a _ n ↦ hFourier T hTH hT a n)

end SHEStochastic.BoundedFourierMildRecognition
