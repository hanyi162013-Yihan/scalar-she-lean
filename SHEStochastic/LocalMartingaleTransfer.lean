module

public import SHEStochastic.BoundedLocalMartingale
public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.LocalMartingaleTransfer
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Transfer a localized native martingale to an adapted continuous
cutoff process before a stopping time. The same argument applies to
short, global and vector-valued equation bookkeeping. -/
theorem stopped {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (μ : Measure Ω) [IsFiniteMeasure μ] (B O : ℝ≥0 → Ω → ℝ)
    (hBa : StronglyAdapted F B) (hBc : ∀ ω, Continuous (B · ω))
    (hOc : ∀ ω, Continuous (O · ω)) (hzero : ∀ ω, B 0 ω=0)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (heq : ∀ᵐ ω ∂μ, ∀ t, stoppedProcess B τ t ω=stoppedProcess O τ t ω)
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : IsLocalizingSequence F σ μ)
    (hm : ∀ n, Martingale (stoppedProcess O (σ n)) F μ) :
    StronglyAdapted F (stoppedProcess B τ) ∧
      Locally (fun X ↦ Martingale X F μ) F (stoppedProcess B τ) μ := by
  have ha := hBa.stoppedProcess hBc hτ
  have hc (ω : Ω) : Continuous (fun t ↦ stoppedProcess B τ t ω) := (hBc ω).stoppedProcess τ
  have hStopped (n : ℕ) : Martingale (stoppedProcess (stoppedProcess B τ) (σ n)) F μ := by
    have hNτ := (hm n).stoppedProcess
      (fun ω t ↦ ((hOc ω).stoppedProcess (σ n)).continuousAt.continuousWithinAt) hτ
    have hComm : stoppedProcess (stoppedProcess O τ) (σ n)=stoppedProcess (stoppedProcess O (σ n)) τ := by
      simp only [stoppedProcess_stoppedProcess']
      congr 1
      funext ω
      exact min_comm _ _
    rw [←hComm] at hNτ
    have hEqN := stoppedProcess_congr (τ:=σ n) heq
    exact hNτ.congr (ha.stoppedProcess hc (hσ.isStoppingTime n))
      (fun t ↦ hEqN.mono fun ω hh ↦ (hh t).symm)
  have hz (ω : Ω) : stoppedProcess B τ 0 ω=0 := by
    rw [stoppedProcess_eq_of_le (show (0:WithTop ℝ≥0)≤τ ω from zero_le)]
    exact hzero ω
  exact ⟨ha,BoundedLocalMartingale.locally_of_stopped μ F _ hz σ hσ hStopped⟩

end SHEStochastic.LocalMartingaleTransfer
