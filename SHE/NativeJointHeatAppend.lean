module

public import SHE.NativeJointHistory

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeJointHeatAppend
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeJointHeatAppend_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointHeatAppend_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {n : ℕ}

def append (Z : Fin n→WordRecursion.Observation) (q ε : ℝ) (x : HeatCircle) : Fin (n+1)→WordRecursion.Observation :=
  Fin.cases ⟨q,q+ε,x⟩ Z

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)

/-- Genuine heat-regularized child observation compatibility. The new
original stop is q and its target is q+epsilon, so it equals S_epsilon Vq;
all old joint observations, with their original stops and targets, agree
exactly with the parent window. Epsilon and the time cutoff stay distinct. -/
theorem value_append_heat (Z : Fin n→WordRecursion.Observation) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(Z i).target) (hqb : q≤b) {ε : ℝ} (hε : 0<ε) (x : HeatCircle) (ω : Ω) :
    NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S (append Z q ε x) q q ω=
      JointPhysicalInsertion.appendState (functional ε x (S.second q ω))
        (NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q ω) := by
  have hchild : ∀ i,(q:ℝ)<(append Z (q:ℝ) ε x i).target := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact lt_add_of_pos_right _ hε
    · exact lt_of_le_of_lt (by exact_mod_cast hqb) (hgap j)
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hh := NativeJointObservations.value_at_original_stop 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (append Z q ε x) q hchild q le_rfl ω 0 rfl
    change _=functional ε x (S.second q ω)
    simpa only [append,Fin.cases_zero,show (q:ℝ)+ε-(q:ℝ)=ε by ring] using hh
  · have hc := NativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (append Z q ε x) q hchild q le_rfl ω j.succ
    have hp := NativeJointObservations.value_eq_physical 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      Z b hgap q hqb ω j
    simp only [append,Fin.cases_succ] at hc
    exact hc.trans hp.symm

end SHE.NativeJointHeatAppend
