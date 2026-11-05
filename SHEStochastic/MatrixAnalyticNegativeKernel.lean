module

public import SHEStochastic.MatrixSignedNegativeHeat
public import SHEStochastic.MatrixAnalyticKernel
public import SHE.HaarWeightedHS

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixAnalyticNegativeKernel
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.CircleHeat SHE.HaarWeightedHeat
open MatrixInfiniteHaar MatrixProfileEntries NativeHeatObservation
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))

theorem component_heat (t : ℝ) (u : Physical (d := d)) (i : d) :
    component i (VectorHeat.heat t u)=RealHeat.realHeat t (component i u) :=
  VectorHeat.coordinate_heat t u i

/-- The output multiplier is applied after the actual heat kernel;
the comparison trace uses the same order of operators. -/
theorem output_heat {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (b : CircleL2) (B : ℝ) (hb : ∀ᵐ x ∂ν, ‖b x‖ ≤ B)
    (t : ℝ) (u : Physical (d := d)) :
    MatrixWeightedOutput.map Λ ρ 0 hΛ hρ b B hb (VectorHeat.heat t u)=
      MatrixWeightedOutput.map Λ ρ t hΛ hρ b B hb u := by
  apply PiLp.ext
  intro i
  change weightedHeat Λ ρ 0 hΛ hρ b B hb (realEmbed (component i (VectorHeat.heat t u)))=
    weightedHeat Λ ρ t hΛ hρ b B hb (realEmbed (component i u))
  rw [component_heat,RealHeat.realEmbed_realHeat]
  change besselHalf Λ ρ hΛ hρ (CircleMultiplier.operator b B hb (heat 0 (heat t (realEmbed (component i u)))))=_
  rw [heat_zero]
  rfl

/-- Signed negative-profile control for the literal analytic-clock
Hilbert--Schmidt kernel. All matrix entries and infinite Haar columns
are retained, with the native-to-analytic time factor explicit. -/
theorem bound {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂ν, ‖b x‖ ≤ B) (P Q : Profile d) :
    ‖HilbertColumns.mapCLM (MatrixWeightedOutput.map Λ ρ 0 hΛ hρ.le b B hb)
      (MatrixAnalyticKernel.kernel t Q-MatrixAnalyticKernel.kernel t P)‖^2 ≤
      MatrixSignedNegativeHeat.constant P Q ρ hρ hρhalf*B^2*timeScale^(1/2 : ℝ)*
        t^(-(1/2 : ℝ))*MatrixNegativeLocalization.energy Λ ρ (MatrixColumnComparison.difference P Q) := by
  have hc : 1 ≤ timeScale := by unfold timeScale; nlinarith [Real.one_le_pi_div_two]
  have ht' : 0 < t/timeScale := div_pos ht timeScale_pos
  have ht1' : t/timeScale ≤ 1 := (div_le_one timeScale_pos).mpr (ht1.trans hc)
  have he (k : d × HaarNode) :
      HilbertColumns.mapCLM (MatrixWeightedOutput.map Λ ρ 0 hΛ hρ.le b B hb)
        (MatrixAnalyticKernel.kernel t Q-MatrixAnalyticKernel.kernel t P) k=
      MatrixSignedNegativeHeat.column Λ ρ (t/timeScale) hΛ hρ.le b B hb P Q k := by
    simp only [HilbertColumns.mapCLM_apply,lp.coeFn_sub,Pi.sub_apply,
      MatrixAnalyticKernel.column,if_pos ht,← map_sub]
    exact output_heat hΛ hρ.le b B hb (t/timeScale) _
  rw [HilbertColumns.norm_sq]
  simp only [he]
  have hh := (MatrixSignedNegativeHeat.energy hΛ hρ hρhalf ht' ht1' b B hB hb P Q).2
  rw [NativeSignedClock.div_neg_rpow ht.le] at hh
  exact hh.trans_eq (by ring)

end SHEStochastic.MatrixAnalyticNegativeKernel
