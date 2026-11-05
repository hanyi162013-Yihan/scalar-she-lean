module

public import SHEStochastic.ScalarUnitTorusFourierEquation
public import SHEStochastic.NativeInverseTimeDilatedFamily
public import SHEStochastic.ScalarBoundedWellPosed
public import SHEStochastic.GlobalCompletedBoundedFourierSolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnitTorusBoundedExistence
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation
open SHE.StoppedFourier SHE.FiniteHaar CanonicalStateDriverFiltration
open ScalarUnitTorusFourierClock (nativeCoefficient nativeBound scale scale_pos)
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

private theorem physical_family {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0)
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B)
    (e : HilbertBasis ι ℝ Noise) (U : ℝ≥0 → Ω → RealL2) (ξ : Ω → RealL2)
    (Q : FiniteScalarIto.Family (filtration F (clock r hr)) μ (r*H) ι)
    (hU : StronglyMeasurable[(filtration F (clock NativeClock.rate NativeClock.rate_pos)).predictable]
      (Function.uncurry U))
    (hn : NullCompleteFiltration.ContainsNullSets (filtration F (clock r hr)) μ)
    (heq : GlobalBoundedFourierRecognition.FourierEquation (filtration F (clock r hr)) μ (r*H)
      U hU (ScalarUnitTorusFourierClock.holder hg) hβ hβ₁ (nativeBound B)
      (ScalarUnitTorusFourierClock.bounded hb) (FiniteCylindricalIto.terminalIto Q.toCoordinates e) ξ) :
    ∃ P : FiniteScalarIto.Family F μ H ι,
      StronglyMeasurable[F.predictable] (Function.uncurry (pullPath r hr U)) ∧
      NullCompleteFiltration.ContainsNullSets F μ ∧
      ScalarUnitTorusFourierEquation.Equation F μ H e (pullPath r hr U) hg hβ hβ₁.le P ξ := by
  let _ : SecondCountableTopology Noise := e.repr.toHomeomorph.secondCountableTopology
  obtain ⟨P,hP⟩ := NativeInverseTimeDilatedFamily.exists_family F μ r hr H Q e hn
  exact ⟨P,pullPath_predictable F r hr U hU,InverseClockLocality.null_complete F μ r hr hn,
    (ScalarUnitTorusFourierEquation.iff_native F μ H e U hU hg hβ hβ₁ B hb P Q hP ξ).mpr heq⟩

/-- Weak existence in the manuscript's time and spatial noise convention. -/
theorem exists_solution (H : ℝ≥0) (hH : 0<H)
    {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B) (c : ℝ) (hc : 0<c) (hEll : ∀ z,c≤|g z|)
    (e : HilbertBasis ι ℝ Noise) (u₀ : RealL2) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (F : Filtration ℝ≥0 m) (μ : @Measure Ω m),
      ∃ (_ : IsProbabilityMeasure μ) (P : FiniteScalarIto.Family F μ H ι) (W : ℝ≥0 → Ω → RealL2),
        StronglyMeasurable[F.predictable] (Function.uncurry W) ∧
        (∀ ω,Continuous (fun t => W t ω)) ∧
        NullCompleteFiltration.ContainsNullSets F μ ∧
        (W 0 =ᵐ[μ] fun _ => u₀) ∧ ScalarUnitTorusFourierEquation.Equation F μ H e W hg hβ hβ₁.le P (W 0) := by
  let _ : SecondCountableTopology Noise := e.repr.toHomeomorph.secondCountableTopology
  let K := r*H
  have hK : 0<K := mul_pos hr hH
  have hc' : 0<scale*c := mul_pos scale_pos hc
  have hell (z : ℝ) : (scale*c)^2≤(nativeCoefficient g z)^2 := by
    rw [←sq_abs (nativeCoefficient g z)]
    exact pow_le_pow_left₀ hc'.le (ScalarUnitTorusFourierClock.elliptic hEll z) 2
  obtain ⟨Q,P,hi,hm⟩ := ScalarBoundedWellPosed.exists_canonical K hK
    (ScalarUnitTorusFourierClock.holder hg) hβ hβ₁ (nativeBound B)
    (ScalarUnitTorusFourierClock.bounded hb) ((scale*c)^2) (sq_pos_of_pos hc') hell e u₀
  let D := filtration (E := RealL2) (ι := ι) K
  let ρ : Measure Unit := Measure.dirac ()
  let Ω := RandomInitialBrownianFamily.Space ρ Q.toMeasure
  let m : MeasurableSpace Ω := inferInstance
  let μ := IndependentNoiseCompletion.measure ρ Q.toMeasure
  let D' := RandomInitialBrownianFamily.filtration ρ Q.toMeasure D
  let Q' := RandomInitialBrownianFamily.family ρ Q.toMeasure D K P
  let U := CompletedBoundedFourierSolution.state Q.toMeasure (state K)
  have hU := CompletedBoundedFourierSolution.predictable D Q.toMeasure (state K) (state_predictable K)
  have hn := RandomInitialBrownianFamily.contains_null ρ Q.toMeasure D
  have hMode := GlobalBoundedFourierRecognition.fourier_of_closed D Q.toMeasure K
    (state K) (state_predictable K) (ScalarUnitTorusFourierClock.holder hg) hβ hβ₁ (nativeBound B)
    (ScalarUnitTorusFourierClock.bounded hb) hK (FiniteCylindricalIto.terminalIto P.toCoordinates e)
    (state K 0) hm
  have hComp := GlobalBoundedFourierPullback.equation (Ξ := Ω) (D := D') Prod.snd
    (IndependentNoiseCompletion.snd_preserving ρ Q.toMeasure)
    (CompletedBoundedFourierSolution.filtered D Q.toMeasure)
    (state K) (state_predictable K) (ScalarUnitTorusFourierClock.holder hg) hβ hβ₁ (nativeBound B)
    (ScalarUnitTorusFourierClock.bounded hb) P Q' e (fun _ _ _ => rfl) (state K 0) hMode
  let F := PredictableTimeDilation.filtration D' (clock r hr).symm
  have hF : PredictableTimeDilation.filtration F (clock r hr) = D' :=
    filtration_inverse_clock r hr D'
  have hs := physical_family F μ H hg hβ hβ₁ B hb e U (U 0)
  rw [hF] at hs
  obtain ⟨P',hP',hnull,hPhysical⟩ := hs Q' hU hn hComp
  let W := pullPath r hr U
  have hzero : W 0=U 0 := by
    change U (r*0) = U 0
    rw [mul_zero]
  have hi' : U 0=ᵐ[μ] fun _ => u₀ :=
    (IndependentNoiseCompletion.snd_preserving ρ Q.toMeasure).quasiMeasurePreserving.ae hi
  refine ⟨Ω,m,F,μ,inferInstance,P',W,hP',?_,hnull,?_,?_⟩
  · exact pullPath_continuous r hr U (fun ω => state_continuous K ω.2)
  · rwa [hzero]
  · rwa [hzero]

end SHEStochastic.ScalarUnitTorusBoundedExistence
