module

public import SHEStochastic.ScalarUnitTorusFourierEquation
public import SHEStochastic.ScalarUnitTorusStateClock
public import SHEStochastic.ScalarBoundedPathLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnitTorusBoundedUniqueness
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation SHE.StoppedFourier SHE.FiniteHaar
open ScalarUnitTorusFourierClock (nativeCoefficient nativeBound scale scale_pos)
open ScalarUnitTorusStateClock (native)
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "Noise" => ScalarVarianceNormalization.Noise
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {ι : Type} [Countable ι] [DecidableEq ι]

private theorem to_native {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : 0<H)
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B)
    (e : HilbertBasis ι ℝ Noise) (P : FiniteScalarIto.Family F μ H ι)
    (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (hcW : ∀ ω, Continuous (fun t => W t ω))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (heq : ScalarUnitTorusFourierEquation.Equation F μ H e W hg hβ hβ₁.le P (W 0)) :
    ∃ Q : FiniteScalarIto.Family (filtration F (clock r hr)) μ (r*H) ι,
      GlobalBoundedFourierRecognition.HasClosedVersion (filtration F (clock r hr)) μ (r*H) (native W)
        (ScalarUnitTorusStateClock.predictable F W hW) (ScalarUnitTorusFourierClock.holder hg)
        hβ hβ₁ (nativeBound B) (ScalarUnitTorusFourierClock.bounded hb) (mul_pos hr hH)
        (FiniteCylindricalIto.terminalIto Q.toCoordinates e) (native W 0) := by
  let _ : SecondCountableTopology Noise := e.repr.toHomeomorph.secondCountableTopology
  obtain ⟨Q,hQ⟩ := NativeTimeDilatedFamily.exists_family F μ r hr H P e hnull
  have hP : ScalarUnitTorusFourierEquation.Equation F μ H e (pullPath r hr (native W))
      hg hβ hβ₁.le P (native W 0) := by
    rw [ScalarUnitTorusStateClock.pull_native,ScalarUnitTorusStateClock.native_zero]
    exact heq
  have he := (ScalarUnitTorusFourierEquation.iff_native F μ H e (native W)
    (ScalarUnitTorusStateClock.predictable F W hW) hg hβ hβ₁ B hb P Q hQ (native W 0)).mp hP
  exact ⟨Q,GlobalBoundedFourierRecognition.exists_closed (filtration F (clock r hr)) μ (r*H)
    (native W) (ScalarUnitTorusStateClock.predictable F W hW) (ScalarUnitTorusFourierClock.holder hg)
    hβ hβ₁ (nativeBound B) (ScalarUnitTorusFourierClock.bounded hb) Q e (native W 0) (mul_pos hr hH)
    (ScalarUnitTorusStateClock.continuous_native W hcW) he⟩

/-- Uniqueness of the manuscript's original bounded scalar state-path law. -/
theorem laws_eq {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : ℝ≥0) (hH : 0<H)
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B) (c : ℝ) (hc : 0<c) (hEll : ∀ z,c≤|g z|)
    (e : HilbertBasis ι ℝ Noise) (u₀ : RealL2)
    (P : FiniteScalarIto.Family F μ H ι) (P' : FiniteScalarIto.Family G ν H ι)
    (W : ℝ≥0 → Ω → RealL2) (Z : ℝ≥0 → Ξ → RealL2)
    (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (hZ : StronglyMeasurable[G.predictable] (Function.uncurry Z))
    (hcW : ∀ ω, Continuous (fun t => W t ω)) (hcZ : ∀ ω, Continuous (fun t => Z t ω))
    (hnW : NullCompleteFiltration.ContainsNullSets F μ) (hnZ : NullCompleteFiltration.ContainsNullSets G ν)
    (hiW : W 0=ᵐ[μ] fun _ => u₀) (hiZ : Z 0=ᵐ[ν] fun _ => u₀)
    (heW : ScalarUnitTorusFourierEquation.Equation F μ H e W hg hβ hβ₁.le P (W 0))
    (heZ : ScalarUnitTorusFourierEquation.Equation G ν H e Z hg hβ hβ₁.le P' (Z 0)) :
    μ.map (NativeContinuousPath.path H W hcW) = ν.map (NativeContinuousPath.path H Z hcZ) := by
  obtain ⟨Q,hQ⟩ := to_native F μ H hH hg hβ hβ₁ B hb e P W hW hcW hnW heW
  obtain ⟨Q',hQ'⟩ := to_native G ν H hH hg hβ hβ₁ B hb e P' Z hZ hcZ hnZ heZ
  have hc' : 0<scale*c := mul_pos scale_pos hc
  have hell (z : ℝ) : (scale*c)^2≤(nativeCoefficient g z)^2 := by
    rw [←sq_abs (nativeCoefficient g z)]
    exact pow_le_pow_left₀ hc'.le (ScalarUnitTorusFourierClock.elliptic hEll z) 2
  have hinitW : native W 0=ᵐ[μ] fun _ => u₀ := ScalarUnitTorusStateClock.native_zero W ▸ hiW
  have hinitZ : native Z 0=ᵐ[ν] fun _ => u₀ := ScalarUnitTorusStateClock.native_zero Z ▸ hiZ
  have hEq := ScalarBoundedPathLaw.laws_eq (filtration F (clock r hr)) (filtration G (clock r hr))
    μ ν (r*H) (mul_pos hr hH) (ScalarUnitTorusFourierClock.holder hg) hβ hβ₁ (nativeBound B)
    (ScalarUnitTorusFourierClock.bounded hb) ((scale*c)^2) (sq_pos_of_pos hc') hell e u₀ Q Q'
    (native W) (native Z) (ScalarUnitTorusStateClock.predictable F W hW)
    (ScalarUnitTorusStateClock.predictable G Z hZ) (ScalarUnitTorusStateClock.continuous_native W hcW)
    (ScalarUnitTorusStateClock.continuous_native Z hcZ) hinitW hinitZ hQ hQ'
  have hMeasW := NativeContinuousPath.measurable_path (r*H) (native W)
    (ScalarUnitTorusStateClock.continuous_native W hcW)
    ((ScalarUnitTorusStateClock.predictable F W hW).mono
      (predictable_le_product (filtration F (clock r hr)))).measurable
  have hMeasZ := NativeContinuousPath.measurable_path (r*H) (native Z)
    (ScalarUnitTorusStateClock.continuous_native Z hcZ)
    ((ScalarUnitTorusStateClock.predictable G Z hZ).mono
      (predictable_le_product (filtration G (clock r hr)))).measurable
  have hp := congrArg (fun q => q.map (ScalarUnitTorusStateClock.pull H)) hEq
  rw [Measure.map_map (ScalarUnitTorusStateClock.measurable_pull H) hMeasW,
    Measure.map_map (ScalarUnitTorusStateClock.measurable_pull H) hMeasZ,
    ScalarUnitTorusStateClock.path_pull,ScalarUnitTorusStateClock.path_pull] at hp
  have hPathW : NativeContinuousPath.path H (pullPath r hr (native W))
      (pullPath_continuous r hr (native W) (ScalarUnitTorusStateClock.continuous_native W hcW)) =
      NativeContinuousPath.path H W hcW := by
    funext ω
    apply ContinuousMap.ext
    intro t
    exact congrFun (congrFun (ScalarUnitTorusStateClock.pull_native W) t.val.toNNReal) ω
  have hPathZ : NativeContinuousPath.path H (pullPath r hr (native Z))
      (pullPath_continuous r hr (native Z) (ScalarUnitTorusStateClock.continuous_native Z hcZ)) =
      NativeContinuousPath.path H Z hcZ := by
    funext ω
    apply ContinuousMap.ext
    intro t
    exact congrFun (congrFun (ScalarUnitTorusStateClock.pull_native Z) t.val.toNNReal) ω
  rwa [hPathW,hPathZ] at hp

end SHEStochastic.ScalarUnitTorusBoundedUniqueness
