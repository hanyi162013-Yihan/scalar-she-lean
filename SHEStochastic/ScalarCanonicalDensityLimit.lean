module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarCanonicalDensityLimit
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X Ω Ξ : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure ν]
    {U : Ω→X} {V : Ξ→X}

/-- A sequence of Borel state-path tests converging in measure in one
realization has a common Borel limit in every realization with the same
state law and the same convergence of the tests. -/
theorem exists_common_limit (hU : Measurable U) (f : ℕ→X→ℝ) (hf : ∀ n,Measurable (f n))
    (J : Ω→ℝ) (hJ : TendstoInMeasure μ (fun n => f n ∘ U) atTop J) :
    ∃ j : X→ℝ,Measurable j ∧ (j ∘ U) =ᵐ[μ] J ∧
      (∀ (V : Ξ→X) (_hV : Measurable V),ν.map V=μ.map U →
        ∀ K : Ξ→ℝ,TendstoInMeasure ν (fun n => f n ∘ V) atTop K → (j ∘ V) =ᵐ[ν] K) := by
  obtain ⟨s,hs,hLim⟩ := hJ.exists_seq_tendsto_ae
  let j := fun x => limUnder atTop (fun n => f (s n) x)
  have hj : Measurable j :=
    (StronglyMeasurable.limUnder (fun n => (hf (s n)).stronglyMeasurable)).measurable
  have hJ' : (j ∘ U) =ᵐ[μ] J :=
    hLim.mono (fun x hx => hx.limUnder_eq)
  refine ⟨j,hj,hJ',?_⟩
  intro V hV hMap K hK
  have hMeas : MeasurableSet {x | Tendsto (fun n => f (s n) x) atTop (𝓝 (j x))} :=
    measurableSet_tendsto_fun (fun n => hf (s n)) hj
  have hA : ∀ᵐ x ∂μ.map U,Tendsto (fun n => f (s n) x) atTop (𝓝 (j x)) := by
    apply (ae_map_iff hU.aemeasurable hMeas).mpr
    filter_upwards [hLim,hJ'] with x hx hEq
    change j (U x)=J x at hEq
    rw [hEq]
    exact hx
  have hB : ∀ᵐ x ∂ν,Tendsto (fun n => (f (s n) ∘ V) x) atTop (𝓝 ((j ∘ V) x)) :=
    (ae_map_iff hV.aemeasurable hMeas).mp (hMap.symm ▸ hA)
  have hM := tendstoInMeasure_of_tendsto_ae (fun n => ((hf (s n)).comp hV).aestronglyMeasurable) hB
  exact tendstoInMeasure_ae_unique hM (hK.comp hs.tendsto_atTop)

/-- Tilting by a Borel function of the state path depends only on the
state-path law. This identity also allows an almost-everywhere version
of the density on the original probability space. -/
theorem map_tilt (hU : Measurable U) (r : X→ℝ≥0∞) (hr : Measurable r)
    (R : Ω→ℝ≥0∞) (hR : R =ᵐ[μ] r ∘ U) :
    (μ.withDensity R).map U=(μ.map U).withDensity r := by
  ext A hA
  rw [Measure.map_apply hU hA,withDensity_apply _ (hU hA),withDensity_apply _ hA,
    setLIntegral_map hA hr hU]
  exact lintegral_congr_ae (ae_restrict_of_ae hR)

end SHEStochastic.ScalarCanonicalDensityLimit
