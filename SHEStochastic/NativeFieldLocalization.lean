module

public import SHEStochastic.LocalizedFieldAssembly
public import SHE.NullCompleteFiltration
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeFieldLocalization
open MeasureTheory Filter SHE
open scoped NNReal Topology

/-- A field locally equal to adapted cutoff fields is adapted. The
cutoff may be selected using the whole future horizon: cofinality gives
an adapted limiting version and null completeness identifies it. -/
theorem adapted {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (t : ℝ≥0)
    (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ ω, Tendsto (fun n ↦ τ n ω) atTop (nhds ⊤))
    (X : ℕ → Ω → ℝ) (hX : ∀ n, StronglyMeasurable[F t] (X n)) (Y : Ω → ℝ)
    (he : ∀ n, ∀ᵐ ω ∂μ, (t:WithTop ℝ≥0)<τ n ω → Y ω=X n ω) : StronglyMeasurable[F t] Y := by
  have hm : StronglyMeasurable[F t] (fun ω ↦ limUnder atTop (fun n ↦ X n ω)) := by
    letI : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder hX
  apply NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t hm
  filter_upwards [ae_all_iff.mpr he] with ω hω
  have ht := hτ ω
  rw [WithTop.tendsto_nhds_top_iff] at ht
  have hlim : Tendsto (fun n ↦ X n ω) atTop (nhds (Y ω)) :=
    tendsto_const_nhds.congr' ((ht t).mono fun n hn ↦ hω n hn)
  exact hlim.limUnder_eq.symm

end SHEStochastic.NativeFieldLocalization
