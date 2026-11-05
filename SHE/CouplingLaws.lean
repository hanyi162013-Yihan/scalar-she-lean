module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import SHE.Laws

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory Filter Topology
open scoped NNReal BoundedContinuousFunction

/-- The L1 coupling error is bounded by the square root of its actual
second moment on a probability space. -/
theorem mean_norm_le_sqrt_energy
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D : Ω → E}
    (hD : MemLp D 2 μ) :
    (∫ ω, ‖D ω‖ ∂μ) ≤ Real.sqrt (∫ ω, ‖D ω‖ ^ (2 : ℕ) ∂μ) := by
  have hD' : MemLp (fun ω => ‖D ω‖) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hD.norm
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hD' h1
  simpa [Real.sqrt_eq_rpow] using h

section Coupling
variable {E : Type*} [NormedAddCommGroup E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The second-moment energy of a genuine coupling measure. -/
def couplingEnergy (π : ProbabilityMeasure (E × E)) : ℝ :=
  ∫ z : E × E, ‖z.1 - z.2‖ ^ (2 : ℕ) ∂(π : Measure (E × E))

omit [BorelSpace E] [SecondCountableTopology E] in
theorem couplingEnergy_nonneg (π : ProbabilityMeasure (E × E)) :
    0 ≤ couplingEnergy π := by
  exact integral_nonneg fun _ => sq_nonneg _

/-- Bounded Lipschitz tests of the two marginals differ by at most the
Lipschitz constant times the square root of the actual coupling energy. -/
theorem coupling_test_bound (π : ProbabilityMeasure (E × E))
    (hπ : MemLp (fun z : E × E => z.1 - z.2) 2 (π : Measure (E × E)))
    (f : E →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    |(∫ x, f x ∂(π.map Prod.fst)) - (∫ x, f x ∂(π.map Prod.snd))| ≤
      (L : ℝ) * Real.sqrt (couplingEnergy π) := by
  have hi1 : Integrable (fun z : E × E => f z.1) (π : Measure (E × E)) :=
    (f.compContinuous ⟨Prod.fst, continuous_fst⟩).integrable _
  have hi2 : Integrable (fun z : E × E => f z.2) (π : Measure (E × E)) :=
    (f.compContinuous ⟨Prod.snd, continuous_snd⟩).integrable _
  have hnorm : Integrable (fun z : E × E => ‖z.1 - z.2‖) (π : Measure (E × E)) :=
    (hπ.integrable (by norm_num)).norm
  have hLip : ∀ z : E × E, ‖f z.1 - f z.2‖ ≤ (L : ℝ) * ‖z.1 - z.2‖ := by
    intro z
    simpa only [dist_eq_norm] using hf.dist_le_mul z.1 z.2
  have hmap1 : (∫ x, f x ∂(π.map Prod.fst)) = ∫ z : E × E, f z.1 ∂π := by
    exact integral_map (by fun_prop) (by exact f.continuous.aestronglyMeasurable)
  have hmap2 : (∫ x, f x ∂(π.map Prod.snd)) = ∫ z : E × E, f z.2 ∂π := by
    exact integral_map (by fun_prop) (by exact f.continuous.aestronglyMeasurable)
  rw [hmap1, hmap2, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z : E × E, ‖f z.1 - f z.2‖ ∂π := norm_integral_le_integral_norm _
    _ ≤ ∫ z : E × E, (L : ℝ) * ‖z.1 - z.2‖ ∂π :=
      integral_mono (hi1.sub hi2).norm (hnorm.const_mul _) hLip
    _ = (L : ℝ) * ∫ z : E × E, ‖z.1 - z.2‖ ∂π := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (mean_norm_le_sqrt_energy _ hπ) L.coe_nonneg

/-- Compare an original marginal to a canonical law after a stopped
change-of-measure estimate for the controlled marginal has been supplied.
That estimate is explicit and is not asserted for an SPDE by this file. -/
theorem coupling_canonical_test_bound
    (π : ProbabilityMeasure (E × E)) (ν : ProbabilityMeasure E) {cost : ℝ}
    (hπ : MemLp (fun z : E × E => z.1 - z.2) 2 (π : Measure (E × E)))
    (f : E →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hchange : |(∫ x, f x ∂(π.map Prod.snd)) - (∫ x, f x ∂ν)| ≤
      2 * ‖f‖ * (Real.sqrt cost + cost)) :
    |(∫ x, f x ∂(π.map Prod.fst)) - (∫ x, f x ∂ν)| ≤
      (L : ℝ) * Real.sqrt (couplingEnergy π) + 2 * ‖f‖ * (Real.sqrt cost + cost) := by
  calc
    _ ≤ |(∫ x, f x ∂(π.map Prod.fst)) - (∫ x, f x ∂(π.map Prod.snd))| +
        |(∫ x, f x ∂(π.map Prod.snd)) - (∫ x, f x ∂ν)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (coupling_test_bound π hπ f hf) hchange

end Coupling
end SHE

namespace SHE
open MeasureTheory Filter Topology
open scoped NNReal BoundedContinuousFunction

/-- The combined coupling and stopped change-of-measure error. -/
def comparisonError (energy cost : ℝ) := Real.sqrt energy + Real.sqrt cost + cost

theorem comparisonError_tends_to_zero {energy cost : ℕ → ℝ}
    (henergy : Tendsto energy atTop (𝓝 0)) (hcost : Tendsto cost atTop (𝓝 0)) :
    Tendsto (fun n => comparisonError (energy n) (cost n)) atTop (𝓝 0) := by
  simpa [comparisonError] using (henergy.sqrt.add hcost.sqrt).add hcost

section Families
variable {E : Type*} [NormedAddCommGroup E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A uniform bounded-Lipschitz majorant with an explicit test-dependent constant. -/
theorem coupling_canonical_scaled_bound
    (π : ProbabilityMeasure (E × E)) (ν : ProbabilityMeasure E) {cost : ℝ}
    (hcost : 0 ≤ cost)
    (hπ : MemLp (fun z : E × E => z.1 - z.2) 2 (π : Measure (E × E)))
    (f : E →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hchange : |(∫ x, f x ∂(π.map Prod.snd)) - (∫ x, f x ∂ν)| ≤
      2 * ‖f‖ * (Real.sqrt cost + cost)) :
    |(∫ x, f x ∂(π.map Prod.fst)) - (∫ x, f x ∂ν)| ≤
      ((L : ℝ) + 2 * ‖f‖) * comparisonError (couplingEnergy π) cost := by
  have h := coupling_canonical_test_bound π ν hπ f hf hchange
  have hn1 := Real.sqrt_nonneg (couplingEnergy π)
  have hn2 : 0 ≤ Real.sqrt cost + cost := by positivity
  have hn3 := norm_nonneg f
  have hn4 : 0 ≤ (L : ℝ) := L.coe_nonneg
  simp only [ProbabilityMeasure.toMeasure_map] at h ⊢
  dsimp [comparisonError]
  nlinarith [mul_nonneg hn3 hn1, mul_nonneg hn4 hn2]

/-- The complete final coupling argument for two prescribed laws. The two
families may live on unrelated probability spaces: each is represented by
its genuine joint law. No limiting canonical law is assumed.

The `hchange` inputs are precisely the standard stopped measure-comparison
estimate still to be supplied by a stochastic construction. The novel SPDE
energy estimate is not assumed under that name. -/
theorem laws_eq_of_coupling_families
    (P Q : ProbabilityMeasure E)
    (πP πQ : ℕ → ProbabilityMeasure (E × E)) (ν : ℕ → ProbabilityMeasure E)
    (costP costQ : ℕ → ℝ)
    (hfirstP : ∀ n, (πP n).map Prod.fst = P)
    (hfirstQ : ∀ n, (πQ n).map Prod.fst = Q)
    (hmomentP : ∀ n, MemLp (fun z : E × E => z.1 - z.2) 2 (πP n : Measure (E × E)))
    (hmomentQ : ∀ n, MemLp (fun z : E × E => z.1 - z.2) 2 (πQ n : Measure (E × E)))
    (hcostP : ∀ n, 0 ≤ costP n) (hcostQ : ∀ n, 0 ≤ costQ n)
    (henergyP : Tendsto (fun n => couplingEnergy (πP n)) atTop (𝓝 0))
    (henergyQ : Tendsto (fun n => couplingEnergy (πQ n)) atTop (𝓝 0))
    (hcostPlim : Tendsto costP atTop (𝓝 0)) (hcostQlim : Tendsto costQ atTop (𝓝 0))
    (hchangeP : ∀ n (f : E →ᵇ ℝ),
      |(∫ x, f x ∂((πP n).map Prod.snd)) - (∫ x, f x ∂(ν n))| ≤
        2 * ‖f‖ * (Real.sqrt (costP n) + costP n))
    (hchangeQ : ∀ n (f : E →ᵇ ℝ),
      |(∫ x, f x ∂((πQ n).map Prod.snd)) - (∫ x, f x ∂(ν n))| ≤
        2 * ‖f‖ * (Real.sqrt (costQ n) + costQ n)) : P = Q := by
  apply laws_eq_of_scaled_common_comparisons P Q ν
    (fun n => comparisonError (couplingEnergy (πP n)) (costP n))
    (fun n => comparisonError (couplingEnergy (πQ n)) (costQ n))
    (comparisonError_tends_to_zero henergyP hcostPlim)
    (comparisonError_tends_to_zero henergyQ hcostQlim)
  intro f hb hl
  obtain ⟨L,hL⟩ := hl
  let F : E →ᵇ ℝ := { toFun := f, continuous_toFun := hL.continuous, map_bounded' := hb }
  have hF : LipschitzWith L F := hL
  have hFcoe : (F : E → ℝ) = f := rfl
  refine ⟨(L : ℝ) + 2 * ‖F‖, ?_⟩
  intro n
  constructor
  · have h := coupling_canonical_scaled_bound (πP n) (ν n) (hcostP n) (hmomentP n) F hF (hchangeP n F)
    simpa only [hfirstP n, hFcoe] using h
  · have h := coupling_canonical_scaled_bound (πQ n) (ν n) (hcostQ n) (hmomentQ n) F hF (hchangeQ n F)
    simpa only [hfirstQ n, hFcoe] using h

end Families
end SHE
