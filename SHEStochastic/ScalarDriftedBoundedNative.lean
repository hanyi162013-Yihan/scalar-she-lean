module

public import SHEStochastic.ScalarDriftedNativeLaw
public import SHEStochastic.ScalarStoppedBoundedBridge
public import SHEStochastic.ScalarBoundedPathLaw
public import SHEStochastic.ScalarBoundedWellPosed
public import SHEStochastic.GlobalCompletedBoundedFourierSolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarDriftedBoundedNative
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
  CanonicalStateDriverFiltration
open ScalarCanonicalObservation ScalarDriftedNativeLaw
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable (H : ℝ≥0) (hH : 0<H) {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g)
  (hβ : 0<β) (hβ₁ : β<1) (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
  (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
  (B : ℝ≥0) (hB : ∀ z,‖g z‖≤B)
  {ι : Type} [Countable ι] [DecidableEq ι] (e : HilbertBasis ι ℝ Noise)

include hell in
private theorem variance_bound : ∀ z,(c : ℝ)^2≤(g z)^2 := fun z =>
  (pow_le_pow_left₀ c.property (hell z) 2).trans_eq (sq_abs _)

include hH hB in
private theorem closed {Ω : Type} [MeasurableSpace Ω]
    (M : Model H hg hβ hβ₁.le b u₀ Ω ι) (hBasis : M.basis=e)
    (hInit : M.W 0 =ᵐ[M.μ] fun _ => u₀) :
    GlobalBoundedFourierRecognition.HasClosedVersion M.F M.μ H M.W M.predictable hg hβ hβ₁ B hB hH
      (FiniteCylindricalIto.terminalIto M.P.toCoordinates e) (M.W 0) := by
  have he := (ScalarStoppedBoundedBridge.iff_bounded M.F M.μ H M.W M.predictable M.continuous
    hg hβ hβ₁ B hB M.P M.basis b u₀ M.nulls).mp M.equation
  rw [hBasis] at he
  apply GlobalBoundedFourierRecognition.exists_closed M.F M.μ H M.W M.predictable hg hβ hβ₁ B hB
    M.P e (M.W 0) hH M.continuous
  intro t ht a n
  filter_upwards [hInit,he t ht a n] with ω h₀ h
  simp only [h₀]
  exact h

include hH hc hell hB in
theorem zero_unique : ZeroUnique H hg hβ hβ₁.le b u₀ e := by
  intro Ω Ξ _ _ M N hMb hNb hiM hiN
  exact ScalarBoundedPathLaw.laws_eq M.F N.F M.μ N.μ H hH hg hβ hβ₁ B hB
    ((c : ℝ)^2) (sq_pos_of_pos (show (0 : ℝ)<c from hc)) (variance_bound c hell) e u₀ M.P N.P
    M.W N.W M.predictable N.predictable M.continuous N.continuous hiM hiN
    (closed H hH hg hβ hβ₁ b u₀ B hB e M hMb hiM) (closed H hH hg hβ hβ₁ b u₀ B hB e N hNb hiN)

include hH hc hell hB in
/-- Native scalar existence with Borel linear-growth drift for the
bounded nondegenerate Hölder coefficient and any deterministic L² initial state. -/
theorem exists_solution :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      Nonempty (@Solution H g C β hg hβ hβ₁.le b u₀ ι _ _ e Ω m) := by
  obtain ⟨Q,P,hi,hm⟩ := ScalarBoundedWellPosed.exists_canonical H hH hg hβ hβ₁ B hB
    ((c : ℝ)^2) (sq_pos_of_pos (show (0 : ℝ)<c from hc)) (variance_bound c hell) e u₀
  let F := filtration (E := RealL2) (ι := ι) H
  let ρ : Measure Unit := Measure.dirac ()
  let Ω := RandomInitialBrownianFamily.Space ρ Q.toMeasure
  let m : MeasurableSpace Ω := inferInstance
  let μ := IndependentNoiseCompletion.measure ρ Q.toMeasure
  let D := RandomInitialBrownianFamily.filtration ρ Q.toMeasure F
  let P' := RandomInitialBrownianFamily.family ρ Q.toMeasure F H P
  let W := CompletedBoundedFourierSolution.state Q.toMeasure (state H)
  have hW := CompletedBoundedFourierSolution.predictable F Q.toMeasure (state H) (state_predictable H)
  have hnull := RandomInitialBrownianFamily.contains_null ρ Q.toMeasure F
  have hp := IndependentNoiseCompletion.snd_preserving ρ Q.toMeasure
  have hcW (ω : Ω) : Continuous (fun t => W t ω) := state_continuous H ω.2
  have hi' : W 0 =ᵐ[μ] fun _ => u₀ := hp.quasiMeasurePreserving.ae hi
  have hf := GlobalBoundedFourierRecognition.fourier_of_closed F Q.toMeasure H (state H) (state_predictable H)
    hg hβ hβ₁ B hB hH (FiniteCylindricalIto.terminalIto P.toCoordinates e) (state H 0) hm
  have hC := GlobalBoundedFourierPullback.equation (Ξ := Ω) (D := D) Prod.snd hp
    (CompletedBoundedFourierSolution.filtered F Q.toMeasure)
    (state H) (state_predictable H) hg hβ hβ₁ B hB P P' e (fun _ _ _ => rfl) (state H 0) hf
  have hDet : GlobalBoundedFourierRecognition.FourierEquation D μ H W hW hg hβ hβ₁ B hB
      (FiniteCylindricalIto.terminalIto P'.toCoordinates e) (fun _ => u₀) := by
    intro t ht a n
    filter_upwards [hi',hC t ht a n] with ω hi h
    change _ - NativeFourierHeatCoordinate.coordinate a n (W 0 ω) = _ at h
    rwa [hi] at h
  have hEq := (ScalarStoppedBoundedBridge.iff_bounded D μ H W hW hcW hg hβ hβ₁ B hB
    P' e b u₀ hnull).mpr hDet
  let M : Model H hg hβ hβ₁.le b u₀ Ω ι := ⟨μ,D,W,hW,hcW,hnull,P',e,hEq⟩
  exact ⟨Ω,m,exists_of_zero c hc hell M rfl hi'⟩

include hH hc hell hB in
theorem exists_unique : ∃! law,Realizes H hg hβ hβ₁.le b u₀ e law := by
  obtain ⟨Ω,m,⟨S⟩⟩ := exists_solution H hH hg hβ hβ₁ b u₀ c hc hell B hB e
  let _ : MeasurableSpace Ω := m
  refine ⟨S.μ.map (NativeContinuousPath.path H S.W S.continuous),⟨Ω,m,S,rfl⟩,?_⟩
  rintro q ⟨Ξ,mΞ,T,rfl⟩
  let _ : MeasurableSpace Ξ := mΞ
  exact laws_eq c hc hell (zero_unique H hH hg hβ hβ₁ b u₀ c hc hell B hB e) T S

end SHEStochastic.ScalarDriftedBoundedNative
