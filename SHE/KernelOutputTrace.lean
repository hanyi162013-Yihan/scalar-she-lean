module

public import SHE.KernelAdjoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.KernelOperator
open MeasureTheory
open scoped ENNReal

/-- A contractive output operator and an arbitrary dependent bounded
right factor preserve the expected actual kernel Hilbert--Schmidt bound.
In particular this discards, rather than postulates, any negative-output
gain on a high-amplitude remainder. -/
theorem expected_output_right_trace_bound
    {W X E F G I J N : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Countable N] (P : Measure W) {ν : Measure X}
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace (Lp E 2 ν)] [BorelSpace (Lp E 2 ν)]
    [MeasurableSpace (Lp F 2 ν)] [BorelSpace (Lp F 2 ν)]
    [MeasurableSpace (Lp ℂ 2 ν)] [BorelSpace (Lp ℂ 2 ν)]
    [SecondCountableTopology (Lp F 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]
    (K : W → Lp E 2 ν) (hK : Measurable K) (Q : E →L[ℂ] F) (hQ : ‖Q‖ ≤ 1)
    (R : W → G →L[ℂ] Lp ℂ 2 ν) (g : HilbertBasis N ℂ G)
    (b : HilbertBasis I ℂ F) (c : HilbertBasis J ℂ (Lp ℂ 2 ν))
    (hRmeas : ∀ n, Measurable (fun ω => R ω (g n)))
    {C A : ℝ} (hC : 0 ≤ C) (hR : ∀ ω, ‖R ω‖^2 ≤ C)
    (hInt : Integrable (fun ω => ‖K ω‖^2) P)
    (hA : (∫ ω, ‖K ω‖^2 ∂P) ≤ A) :
    Integrable (fun ω => ∑' n, ‖(Q.comp ((synthesis (K ω)).comp (R ω))) (g n)‖^2) P ∧
      (∫ ω, ∑' n, ‖(Q.comp ((synthesis (K ω)).comp (R ω))) (g n)‖^2 ∂P) ≤ C*A := by
  let K' : W → Lp F 2 ν := fun ω => Q.compLp (K ω)
  have hm : Measurable K' := (Q.compLpL 2 ν).continuous.measurable.comp hK
  have hn (ω : W) : ‖K' ω‖ ≤ ‖K ω‖ :=
    (Q.norm_compLp_le (K ω)).trans ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
  have hs (ω : W) : ‖K' ω‖^2 ≤ ‖K ω‖^2 := pow_le_pow_left₀ (norm_nonneg _) (hn ω) 2
  have hi : Integrable (fun ω => ‖K' ω‖^2) P := by
    apply hInt.mono' (hm.norm.pow_const (2:ℕ)).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hs ω)
  have ha : (∫ ω, ‖K' ω‖^2 ∂P) ≤ A := (integral_mono hi hInt hs).trans hA
  have h := expected_synthesis_right_trace_bound P K' R b c g hm hRmeas hC hR hi ha
  have he (ω : W) : (synthesis (K' ω)).comp (R ω)=Q.comp ((synthesis (K ω)).comp (R ω)) := by
    change (synthesis (Q.compLp (K ω))).comp (R ω)=_
    rw [synthesis_compLp,ContinuousLinearMap.comp_assoc]
  simpa only [he] using h

end SHE.KernelOperator
