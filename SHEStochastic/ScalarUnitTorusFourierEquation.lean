module

public import SHEStochastic.ScalarUnitTorusFourierClock
public import SHEStochastic.GlobalBoundedFourierRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnitTorusFourierEquation
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal
open ScalarUnitTorusFourierClock (nativeCoefficient nativeBound)

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν₂
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (e : HilbertBasis ι ℝ Noise)

local notation "Fₙ" => filtration F (clock r hr)
local notation "Hₙ" => r*H

/-- The manuscript's scalar drift-free equation tested on the real
and imaginary Fourier coordinates. The noise row is the original
signed coefficient with unit spatial Haar mass. -/
def Equation (W : ℝ≥0 → Ω → RealL2) {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g)
    (hβ : 0<β) (hβ₁ : β≤1) (P : FiniteScalarIto.Family F μ H ι) (ξ : Ω → RealL2) : Prop :=
  ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ), ∃ v : Process (E := Noise) F μ H,
    v =ᵐ[energyMeasure μ H] ScalarUnitTorusFourierClock.row H W hg hβ hβ₁ a n ∧
      ∀ (T : ℝ≥0), T≤H →
        (fun ω => Real.exp ((r : ℝ)*(T : ℝ)*(n : ℝ)^2)*φ a n (W T ω)-φ a n (ξ ω)) =ᵐ[μ]
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
            (StoppedItoInputs.stop F μ H T v)

variable (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[(filtration F (clock NativeClock.rate NativeClock.rate_pos)).predictable]
    (Function.uncurry U))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
  (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B)
  (P : FiniteScalarIto.Family F μ H ι)
  (Q : FiniteScalarIto.Family (filtration F (clock NativeClock.rate NativeClock.rate_pos))
    μ (NativeClock.rate*H) ι)

local notation "Jn" => FiniteCylindricalIto.terminalIto Q.toCoordinates e
local notation "Jp" => FiniteCylindricalIto.terminalIto P.toCoordinates e
local notation "gₙ" => ScalarUnitTorusFourierClock.holder hg
local notation "Bₙ" => nativeBound B
local notation "hBₙ" => ScalarUnitTorusFourierClock.bounded hb
local notation "W" => pullPath r hr U

private theorem stop_transport
    (hTransport : ∀ v : Process (E := Noise) (filtration F (clock r hr)) μ (r*H),
      (Jn).integral v = (Jp).integral (processIsometry F μ r hr H v))
    (a : ℂ →L[ℝ] ℝ) (n : ℤ) (T : ℝ≥0) :
    (Jn).integral (StoppedItoInputs.stop Fₙ μ Hₙ (clock r hr T)
      (BoundedFourierInput.input Fₙ μ Hₙ U hU gₙ hβ hβ₁ Bₙ hBₙ a n)) =
    (Jp).integral (StoppedItoInputs.stop F μ H T
      (ScalarUnitTorusFourierClock.input F μ H U hU hg hβ hβ₁ B hb a n)) := by
  rw [hTransport,ClockedItoAlgebra.map_stop F μ r hr H]
  have hT : (clock r hr T : ℝ≥0) / (r : ℝ) = (T : ℝ) := by
    change ((r : ℝ)*(T : ℝ))/(r : ℝ) = _
    rw [mul_comm,mul_div_cancel_right₀ _ (show (r : ℝ)≠0 from (show (0 : ℝ)<r from hr).ne')]
  rw [hT]
  rfl

/-- Exact two-way transport of the original Fourier stochastic
equation, including all times, all modes and the original stops. -/
theorem iff_native
    (hTransport : ∀ v : Process (E := Noise) (filtration F (clock r hr)) μ (r*H),
      (Jn).integral v = (Jp).integral (processIsometry F μ r hr H v))
    (ξ : Ω → RealL2) :
    Equation F μ H e W hg hβ hβ₁.le P ξ ↔
      GlobalBoundedFourierRecognition.FourierEquation Fₙ μ Hₙ U hU
        gₙ hβ hβ₁ Bₙ hBₙ Jn ξ := by
  have hT (T : ℝ≥0) (hT : T≤H) : clock r hr T≤r*H :=
    (clock r hr).monotone hT
  constructor
  · intro heq S hS a n
    let T := (clock r hr).symm S
    have hts : clock r hr T = S := (clock r hr).apply_symm_apply S
    have ht : T≤H := by
      apply (clock r hr).le_iff_le.mp
      rw [hts]
      exact hS
    obtain ⟨v,hv,he⟩ := heq a n
    have hv' := ScalarUnitTorusFourierClock.input_ae F μ H U hU hg hβ hβ₁ B hb a n
    have hEq : v=ScalarUnitTorusFourierClock.input F μ H U hU hg hβ hβ₁ B hb a n :=
      PastItoAlgebra.eq_of_ambient_ae F μ H (hv.trans hv'.symm)
    have hp := he T ht
    rw [hEq,←stop_transport F μ H e U hU hg hβ hβ₁ B hb P Q hTransport a n T,hts] at hp
    have hs : (r : ℝ)*(T : ℝ)=(S : ℝ) := congrArg NNReal.toReal hts
    simpa only [hs,pullPath,hts] using hp
  · intro heq a n
    refine ⟨ScalarUnitTorusFourierClock.input F μ H U hU hg hβ hβ₁ B hb a n,
      ScalarUnitTorusFourierClock.input_ae F μ H U hU hg hβ hβ₁ B hb a n,?_⟩
    intro T ht
    have hs := heq (clock r hr T) (hT T ht) a n
    rw [stop_transport F μ H e U hU hg hβ hβ₁ B hb P Q hTransport a n T] at hs
    exact hs

end SHEStochastic.ScalarUnitTorusFourierEquation
