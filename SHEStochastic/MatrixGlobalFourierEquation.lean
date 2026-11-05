module

public import SHEStochastic.MatrixGlobalFourierStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixGlobalFourierEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixFourierCoordinates
open MatrixGlobalFourierStep
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {H : ℝ≥0} {G : MatrixNonlinearCoefficient.Coefficient (Fin n)} {C β : ℝ≥0}
    {hG : HolderWith C β G.value} {hβ : 0<β} {hβ1 : β≤1} {hH : (H : ℝ)≤1}
    (D : MatrixFourierBlockChain.Data H G hG hβ hβ1 hH)
    (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (hH0 : 0<H)

/-- Finite telescoping of the actual Fourier equations on the single
global probability space. All martingale terms use one fixed global
native integral and one fixed global state-dependent input. -/
theorem bounded (T : ℝ≥0) (M : ℕ) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (m : ℤ) :
    (M : ℝ≥0)*H≤T → ∀ t : ℝ≥0,t≤(M : ℝ≥0)*H →
      (fun p => Real.exp ((t : ℝ)*(m : ℝ)^2)*coordinate i a m (MatrixGlobalBlockPath.state H t p)) =ᵐ[D.base.law ρ₀]
        fun p => coordinate i a m (MatrixGlobalBlockPath.state H 0 p)+value D ρ₀ hH0 T t i a m p := by
  induction M with
  | zero =>
      intro hMT t ht
      have ht0 : t=0 := le_antisymm (by simpa only [Nat.cast_zero,zero_mul] using ht) bot_le
      subst t
      have hz : value D ρ₀ hH0 T 0 i a m =ᵐ[D.base.law ρ₀] fun _ => 0 := by
        unfold value
        rw [NNReal.coe_zero,StoppedItoInputs.stop_zero,map_zero]
        exact Lp.coeFn_zero _ _ _
      filter_upwards [hz] with p hp
      simp only [NNReal.coe_zero,zero_mul,Real.exp_zero,one_mul,hp,add_zero]
  | succ M ih =>
      intro hMT t ht
      let v : ℝ≥0 := (M : ℝ≥0)*H
      have hcover : v+H≤T := by simpa only [v,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hMT
      have hprev : v≤T := le_trans le_self_add hcover
      by_cases htv : t≤v
      · exact ih hprev t htv
      · have hvt : v≤t := le_of_not_ge htv
        have hs : t-v≤H := by
          apply tsub_le_iff_right.mpr
          simpa only [v,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using ht
        have hp := ih hprev v le_rfl
        have hn := step D ρ₀ hH0 T M hcover i a m (t-v) hs
        change (fun p => Real.exp (((v+(t-v) : ℝ≥0) : ℝ)*(m : ℝ)^2)*coordinate i a m
          (MatrixGlobalBlockPath.state H (v+(t-v)) p)) =ᵐ[D.base.law ρ₀]
          fun p => Real.exp ((v : ℝ)*(m : ℝ)^2)*coordinate i a m (MatrixGlobalBlockPath.state H v p)+
            value D ρ₀ hH0 T (v+(t-v)) i a m p-value D ρ₀ hH0 T v i a m p at hn
        rw [add_tsub_cancel_of_le hvt] at hn
        filter_upwards [hp,hn] with p hp hn
        rw [hp] at hn
        exact hn.trans (by ring)

/-- Every finite union of continuation blocks is a genuine native
Fourier solution in the full global physical state-and-driver filtration. -/
theorem equation (M : ℕ) :
    MatrixFourierMildRealization.RandomEquation (MatrixBlockNaturalFiltration.filtration H) (D.base.law ρ₀)
      ((M : ℝ≥0)*H) (MatrixSmoothCoefficient.coefficient G 0)
      (MatrixBoundedContinuationKernel.target_holder G hG) hβ hβ1
      MatrixGlobalFourierStep.state (predictable hH0)
      (MatrixGlobalBrownianPast.family D.base ρ₀ hH0 ((M : ℝ≥0)*H))
      (MatrixGlobalBlockPath.state H 0) := by
  intro i a m t ht
  exact bounded D ρ₀ hH0 ((M : ℝ≥0)*H) M i a m le_rfl t ht

end SHEStochastic.MatrixGlobalFourierEquation
