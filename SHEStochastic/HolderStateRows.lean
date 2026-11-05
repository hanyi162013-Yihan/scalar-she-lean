module

public import SHEStochastic.HolderCoefficientIntegrability
public import SHEStochastic.HolderWeightedEnergy
public import SHEStochastic.FamilyLpRepresentative
public import SHEStochastic.LpSections
public import SHEStochastic.ContinuousKernelLpAction
public import SHE.NativeHeatSpan
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.HolderStateRows
open MeasureTheory SHE SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {P E V : Type*} [MeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (U : P → Lp E 2 (haarAddCircle (T := 2 * Real.pi))) (hU : StronglyMeasurable U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (k : P → C(HeatCircle, ℝ))

def raw (p : P × HeatCircle) : V :=
  k p.1 p.2 • G (FamilyLpRepresentative.representative haarAddCircle U hU p)

include hG hβ hβ1 in
theorem memLp (p : P) : MemLp (fun x ↦ raw U hU k (G := G) (p, x)) 2 haarAddCircle := by
  have hc := HolderCoefficientIntegrability.memLp_two hβ hβ1 hG (Lp.memLp (U p))
  have hr : MemLp (fun x ↦ G (FamilyLpRepresentative.representative haarAddCircle U hU (p, x))) 2 haarAddCircle :=
    hc.ae_eq ((FamilyLpRepresentative.representative_ae haarAddCircle U hU p).symm.mono fun _ hx ↦ congrArg G hx)
  exact ((k p).memLp ℝ (p := ⊤) (μ := haarAddCircle)).smul hr

def row (p : P) : Lp V 2 (haarAddCircle (T := 2 * Real.pi)) :=
  (memLp U hU hG hβ hβ1 k p).toLp _

theorem row_ae (p : P) : row U hU hG hβ hβ1 k p =ᵐ[haarAddCircle]
    fun x ↦ k p x • G (U p x) := by
  filter_upwards [(memLp U hU hG hβ hβ1 k p).coeFn_toLp,
    FamilyLpRepresentative.representative_ae haarAddCircle U hU p] with x hx hr
  exact hx.trans (by dsimp [raw]; rw [hr])

theorem row_operator (p : P) : row U hU hG hβ hβ1 k p =
    ContinuousKernelLpAction.operator haarAddCircle
      (HolderCoefficientIntegrability.coefficient hβ hβ1 hG (U p)) (k p) := by
  apply Lp.ext
  filter_upwards [row_ae U hU hG hβ hβ1 k p,
    ContinuousKernelLpAction.operator_ae haarAddCircle
      (HolderCoefficientIntegrability.coefficient hβ hβ1 hG (U p)) (k p),
    HolderCoefficientIntegrability.coefficient_ae hβ hβ1 hG (U p)] with x hr ho hc
  rw [hr, ho, hc]

/-- The row depends only on the current L² state, even though the
joint representatives were chosen separately for the two families. -/
theorem row_state_congr (W : P → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hW : StronglyMeasurable W) (p : P) (hp : U p = W p) :
    row U hU hG hβ hβ1 k p = row W hW hG hβ hβ1 k p := by
  apply Lp.ext
  filter_upwards [row_ae U hU hG hβ hβ1 k p, row_ae W hW hG hβ hβ1 k p] with x hu hw
  exact hu.trans (by rw [hp]; exact hw.symm)

/-- Joint strong measurability is obtained from the existing L²-section
theorem. This works also with the predictable sigma algebra as P. -/
theorem stronglyMeasurable (hk : Measurable (fun p : P × HeatCircle ↦ k p.1 p.2)) :
    StronglyMeasurable (row U hU hG hβ hβ1 k) := by
  have hr := FamilyLpRepresentative.representative_measurable haarAddCircle U hU
  have hg := (hG.uniformContinuous hβ).continuous.measurable.comp hr
  have hraw : StronglyMeasurable (raw U hU k (G := G)) := (hk.smul hg).stronglyMeasurable
  exact LpSections.stronglyMeasurable_of_joint haarAddCircle (row U hU hG hβ hβ1 k)
    (raw U hU k (G := G)) hraw (fun p ↦ (memLp U hU hG hβ hβ1 k p).coeFn_toLp)

/-- The constructed Hilbert row has exactly the physical coefficient
energy. No measurable choice of point evaluations of L² classes is assumed. -/
theorem energy (p : P) : ENNReal.ofReal (‖row U hU hG hβ hβ1 k p‖ ^ 2) =
    ∫⁻ x, ENNReal.ofReal ((k p x) ^ 2 * ‖G (U p x)‖ ^ 2) ∂haarAddCircle := by
  rw [← HolderWeightedEnergy.state_mass (row U hU hG hβ hβ1 k p)]
  apply lintegral_congr_ae
  filter_upwards [row_ae U hU hG hβ hβ1 k p] with x hx
  rw [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem difference_energy (l : P → C(HeatCircle, ℝ)) (p : P) :
    ENNReal.ofReal (‖row U hU hG hβ hβ1 k p - row U hU hG hβ hβ1 l p‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal ((k p x - l p x) ^ 2 * ‖G (U p x)‖ ^ 2) ∂haarAddCircle := by
  rw [← HolderWeightedEnergy.state_mass (row U hU hG hβ hβ1 k p - row U hU hG hβ hβ1 l p)]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub (row U hU hG hβ hβ1 k p) (row U hU hG hβ hβ1 l p),
    row_ae U hU hG hβ hβ1 k p, row_ae U hU hG hβ hβ1 l p] with x hs hk hl
  rw [hs]
  change ENNReal.ofReal (‖row U hU hG hβ hβ1 k p x - row U hU hG hβ hβ1 l p x‖ ^ 2) = _
  rw [hk, hl, ← sub_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Physical energy finiteness produces the actual L² family of Hilbert
rows, including for a predictable trim of the time-probability measure. -/
theorem memLp_family (hk : Measurable (fun p : P × HeatCircle ↦ k p.1 p.2)) (η : Measure P)
    (henergy : (∫⁻ p, ∫⁻ x, ENNReal.ofReal ((k p x) ^ 2 * ‖G (U p x)‖ ^ 2) ∂haarAddCircle ∂η) < ⊤) :
    MemLp (row U hU hG hβ hβ1 k) 2 η := by
  have hm := stronglyMeasurable U hU hG hβ hβ1 k hk
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨(hm.norm.pow 2).aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖‖row U hU hG hβ hβ1 k p‖ ^ 2‖ₑ ∂η) < ⊤
  convert henergy using 1
  apply lintegral_congr
  intro p
  rw [Real.enorm_eq_ofReal (sq_nonneg _), energy U hU hG hβ hβ1 k p]

end SHEStochastic.HolderStateRows
