module

public import SHE.NativeJointObservations
public import SHE.JointWordObserve
public import SHE.PredictableWordState

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.NativeJointHistory
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointHistory_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointHistory_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointHistory_circleSigma : MeasurableSpace CircleL2 := borel _
local instance nativeJointHistory_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)

def firstData : PredictableWordState.Data 𝓕 μ H := ⟨Function.uncurry S.first,S.first_predictable⟩
def secondData : PredictableWordState.Data 𝓕 μ H := ⟨Function.uncurry S.second,S.second_predictable⟩

def evaluate {n : ℕ} (Z : Fin n→WordRecursion.Observation) (ω : Ω) (t : ℝ) : WordRecursion.State n :=
  JointWordObserve.evaluate Λ
    (fun r => (firstData 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S).physicalState (ω,r))
    (fun r => (secondData 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S).physicalState (ω,r))
    (fun tx => (firstData 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S).physicalField (ω,tx))
    (fun tx => (secondData 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S).physicalField (ω,tx)) Z t

/-- The actual joint martingale is the physical joint observation used
in recursive words, on every covered positive-gap common window. -/
theorem evaluate_eq_value {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b) (ω : Ω) :
    evaluate 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z ω (q:ℝ)=
      NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q ω := by
  apply PiLp.ext
  intro i
  rw [NativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap q hqb ω i]
  have hqT : (q:ℝ)<(Z i).target := lt_of_le_of_lt (by exact_mod_cast hqb) (hgap i)
  simp only [evaluate,JointWordObserve.evaluate,WithLp.ofLp_toLp,WordRecursion.observe,ite_eq_left hqT,
    firstData,secondData,PredictableWordState.Data.physicalState,Real.toNNReal_coe,Function.uncurry]
  rw [← functional_physical (sub_pos.mpr hqT),← functional_physical (sub_pos.mpr hqT),map_sub]

/-- Changing the auxiliary covered terminal window never changes any
actual old joint coordinate before both windows. -/
theorem value_common_window_eq {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b c q : ℝ≥0)
    (hbWin : ∀ i,(b:ℝ)<(Z i).target) (hcWin : ∀ i,(c:ℝ)<(Z i).target)
    (hqb : q≤b) (hqc : q≤c) (ω : Ω) :
    NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q ω=
      NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z c q ω := by
  exact (evaluate_eq_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q hbWin hqb ω).symm.trans
    (evaluate_eq_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z c q hcWin hqc ω)

end SHE.NativeJointHistory
