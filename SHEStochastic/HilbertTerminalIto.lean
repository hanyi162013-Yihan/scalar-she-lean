module

public import SHE.StandardTerminalIto
public import SHEStochastic.HilbertIsometryLift
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.HilbertTerminalIto
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns ColumnsHilbertSum
open scoped ENNReal NNReal Topology

variable {Ω ι κ E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable κ]
  (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)
  (b : HilbertBasis κ ℝ E)
  (J : StandardTerminalIto (C := Space ι ℝ) (E := ℝ) 𝓕 μ H)

local notation "ν" => (energyMeasure μ H).trim (predictable_le_product 𝓕)

def integral : Process (E := Space ι E) 𝓕 μ H →ₗᵢ[ℝ] Lp E 2 μ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact HilbertIsometryLift.operator ν μ b J.integral

theorem commutes (L : E →L[ℝ] ℝ) (v : Process (E := Space ι E) 𝓕 μ H) :
    (L.compLpL 2 μ) (integral 𝓕 μ H b J v) =
      J.integral (((mapCLM L).compLpL 2 ν) v) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact HilbertIsometryLift.commutes ν μ b J.integral L v

theorem centered (v : Process (E := Space ι E) 𝓕 μ H) :
    ∫ ω, integral 𝓕 μ H b J v ω ∂μ = 0 := by
  by_cases hi : Integrable (integral 𝓕 μ H b J v : Ω → E) μ
  · apply ext_inner_left ℝ
    intro c
    let L : E →L[ℝ] ℝ := innerSL ℝ c
    have hrep : (fun ω => L (integral 𝓕 μ H b J v ω)) =ᵐ[μ]
        J.integral (((mapCLM L).compLpL 2 ν) v) := by
      have h := L.coeFn_compLpL (integral 𝓕 μ H b J v)
      rw [commutes 𝓕 μ H b J L v] at h
      exact h.symm
    change L (∫ ω, integral 𝓕 μ H b J v ω ∂μ) = L 0
    rw [map_zero, ← L.integral_comp_comm hi, integral_congr_ae hrep, J.centered]
  · rw [integral_undef hi]

def coefficient (v : Process (E := Space ι E) 𝓕 μ H) (j : κ) :
    Process (E := Space ι ℝ) 𝓕 μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact HilbertIsometryLift.sourceEquiv ν b v j

theorem coordinate_stopped (l : ℝ≥0) (v : Process (E := Space ι E) 𝓕 μ H)
    (hv : ∀ᵐ p ∂energyMeasure μ H, l < p.1 → v p = 0) (j : κ) :
    ∀ᵐ p ∂energyMeasure μ H, l < p.1 →
      coefficient 𝓕 μ H b v j p = 0 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  change ∀ᵐ p ∂energyMeasure μ H, l < p.1 → HilbertIsometryLift.sourceEquiv ν b v j p = 0
  rw [HilbertIsometryLift.source_coordinate]
  filter_upwards [ae_eq_of_ae_eq_trim ((mapCLM (innerSL ℝ (b j))).coeFn_compLpL v), hv]
    with p hp hs hl
  rw [hp, hs hl, map_zero]

theorem adapted (l : ℝ≥0) (v : Process (E := Space ι E) 𝓕 μ H)
    (hv : ∀ᵐ p ∂energyMeasure μ H, l < p.1 → v p = 0) :
    ∃ Z : Ω → E, StronglyMeasurable[𝓕 l] Z ∧
      integral 𝓕 μ H b J v =ᵐ[μ] Z := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  let f := HilbertIsometryLift.sourceEquiv ν b v
  let Y (j : κ) := L2HilbertSum.lift μ (unit b j) (J.integral (f j))
  have hY (j : κ) : AEStronglyMeasurable[𝓕 l] (Y j : Ω → E) μ := by
    obtain ⟨Z, hZ, hrep⟩ := J.adapted l (f j) (coordinate_stopped 𝓕 μ H b l v hv j)
    refine ⟨fun ω => unit b j (Z ω), (unit b j).continuous.comp_stronglyMeasurable hZ, ?_⟩
    exact (L2HilbertSum.lift_ae μ (unit b j) _).trans (hrep.fun_comp (unit b j))
  have hs (s : Finset κ) : AEStronglyMeasurable[𝓕 l] (∑ j ∈ s, Y j : Lp E 2 μ) μ := by
    apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp
    exact Submodule.sum_mem (lpMeas E ℝ (𝓕 l) 2 μ)
      (fun j _ => mem_lpMeas_iff_aestronglyMeasurable.mpr (hY j))
  have hc : IsClosed {g : Lp E 2 μ | AEStronglyMeasurable[𝓕 l] (g : Ω → E) μ} :=
    isClosed_aestronglyMeasurable (𝓕.le l)
  have hlim : HasSum Y (integral 𝓕 μ H b J v) :=
    HilbertIsometryLift.operator_hasSum ν μ b J.integral v
  have hmeas := hc.mem_of_tendsto hlim (Filter.Eventually.of_forall hs)
  exact ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk⟩

/-- The complete Hilbert-valued terminal integral, derived from the
scalar integral without an additional stochastic hypothesis. -/
def terminalIto : StandardTerminalIto (C := Space ι E) (E := E) 𝓕 μ H where
  integral := integral 𝓕 μ H b J
  adapted := adapted 𝓕 μ H b J
  centered := centered 𝓕 μ H b J

end SHEStochastic.HilbertTerminalIto
