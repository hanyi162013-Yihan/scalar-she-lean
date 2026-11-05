module

public import SHEStochastic.MatrixUnboundedGlobalFourierStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalFourierEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

/-- Finite telescoping of the literal unbounded matrix Fourier
equations under one global Brownian family and one global input. -/
theorem bounded (T : ℝ≥0) (M : ℕ) (i : Fin n)
    (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (M : ℝ≥0)*1≤T → ∀ t : ℝ≥0,t≤(M : ℝ≥0)*1 →
      (fun p => Real.exp ((t : ℝ)*(m : ℝ)^2)*coordinate i a m
        (MatrixGlobalBlockPath.state 1 t p)) =ᵐ[S.law.toMeasure]
        fun p => coordinate i a m (MatrixGlobalBlockPath.state 1 0 p)+
          MatrixUnboundedGlobalFourierStep.value S T t i a m p := by
  induction M with
  | zero =>
      intro hMT t ht
      have ht0 : t=0 := le_antisymm (by simpa only [Nat.cast_zero,zero_mul] using ht) bot_le
      subst t
      have hz : MatrixUnboundedGlobalFourierStep.value S T 0 i a m =ᵐ[S.law.toMeasure]
          fun _ => 0 := by
        unfold MatrixUnboundedGlobalFourierStep.value
        rw [NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero]
        exact Lp.coeFn_zero _ _ _
      filter_upwards [hz] with p hp
      simp only [NNReal.coe_zero,zero_mul,Real.exp_zero,one_mul,hp,add_zero]
  | succ M ih =>
      intro hMT t ht
      let v : ℝ≥0 := (M : ℝ≥0)*1
      have hcover : v+1≤T := by
        simpa only [v,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hMT
      have hprev : v≤T := le_trans le_self_add hcover
      by_cases htv : t≤v
      · exact ih hprev t htv
      · have hvt : v≤t := le_of_not_ge htv
        have hs : t-v≤1 := by
          apply tsub_le_iff_right.mpr
          simpa only [v,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using ht
        have hp := ih hprev v le_rfl
        have hn := MatrixUnboundedGlobalFourierStep.step S T M hcover i a m (t-v) hs
        change (fun p => Real.exp (((v+(t-v) : ℝ≥0) : ℝ)*(m : ℝ)^2)*coordinate i a m
          (MatrixGlobalBlockPath.state 1 (v+(t-v)) p)) =ᵐ[S.law.toMeasure]
          fun p => Real.exp ((v : ℝ)*(m : ℝ)^2)*coordinate i a m
            (MatrixGlobalBlockPath.state 1 v p)+
            MatrixUnboundedGlobalFourierStep.value S T (v+(t-v)) i a m p-
            MatrixUnboundedGlobalFourierStep.value S T v i a m p at hn
        rw [add_tsub_cancel_of_le hvt] at hn
        filter_upwards [hp,hn] with p hp hn
        rw [hp] at hn
        exact hn.trans (by ring)

/-- On each finite integer horizon the single pasted vector state
solves the original unbounded Fourier equation from time zero. -/
theorem equation (M : ℕ) :
    MatrixUnboundedFourierPullback.Equation G hG hβ hβ1.le
      (MatrixUnboundedGlobalFourierStep.state (n := n))
      (MatrixUnboundedGlobalFourierStep.predictable (n := n))
      (MatrixUnboundedGlobalEnergy.finite_energy S (M : ℝ≥0))
      (S.family (M : ℝ≥0)) (MatrixGlobalBlockPath.state 1 0) := by
  intro i a m t ht
  exact bounded S (M : ℝ≥0) M i a m (by simp) t (by simpa only [mul_one] using ht)

end SHEStochastic.MatrixUnboundedGlobalFourierEquation
