module

public import SHEStochastic.MatrixUnboundedCutoff
public import SHEStochastic.SublinearHeatCoefficientEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixUnboundedHeatRows
open MeasureTheory SHE SHE.StoppedFourier AddCircle MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β)
    (ell : ℝ) (hell : 0 < ell) (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R

theorem zero (R : ℝ≥0) : (G_R R).value 0=G 0 :=
  MatrixUnboundedCutoff.agrees G hG hβ ell hell hLower R (by simp)

/-- One radius-independent estimate covers all spatial heat rows and
their increments. It is the existing generic Holder energy theorem
applied to the matrix cutoff, whose Holder constant and origin agree. -/
theorem weighted {X : Type*} [MeasurableSpace X] (ν : Measure X) (hβ1 : β ≤ 1)
    (R : ℝ≥0) (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
    (h : X → ℝ≥0∞) (hh : AEMeasurable h ν) (L Q : ℝ≥0∞)
    (hcap : ∀ᵐ x ∂ν,h x ≤ L) (henergy : (∫⁻ x,h x ∂ν) ≤ Q) :
    (∫⁻ x,h x*ENNReal.ofReal (‖(G_R R).value (u x)‖^2) ∂ν) ≤
      ENNReal.ofReal (2*(‖G 0‖+(C : ℝ))^2)*
        (Q+L^(β : ℝ)*(Q^(1-(β : ℝ))*ENNReal.ofReal (‖u‖^2)^(β : ℝ))) := by
  have hb := HolderWeightedEnergy.bound
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower R) hβ1 u h hh L Q hcap henergy
  simpa only [zero G hG hβ ell hell hLower R] using hb

/-- The actual positive native heat row has the integrable sublinear
time exponent, uniformly in the coefficient truncation radius. -/
theorem heat (hβ1 : β ≤ 1) (R : ℝ≥0)
    (u : Lp (EuclideanSpace ℝ (Fin n)) 2 haarAddCircle)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (a : HeatCircle) :
    (∫⁻ x,ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖^2*‖(G_R R).value (u x)‖^2) ∂haarAddCircle) ≤
      ENNReal.ofReal (2*(‖G 0‖+(C : ℝ))^2*
        ScaledHeatTraceEnvelope.constant 1 2^(1+(β : ℝ))*t^(-(1+(β : ℝ))/2))*
          (1+ENNReal.ofReal (‖u‖^2)^(β : ℝ)) := by
  have hb := SublinearHeatCoefficientEnergy.small_time_bound
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower R) hβ1 u ht ht1 a
  simpa only [zero G hG hβ ell hell hLower R] using hb

end SHEStochastic.MatrixUnboundedHeatRows
