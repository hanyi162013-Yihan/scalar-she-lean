module

public import SHE.StandardFiniteIto
public import SHE.NativeItoBracket

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FiniteItoCovarianceBounds
open Set MeasureTheory PredictableL2 GaussianItoTest
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable {n : ℕ} (R : Fin n→Process (E:=C) 𝓕 μ H)

/-- The chosen original predictable row representatives give genuine
Borel covariance entries on the physical real clock. -/
theorem entry_measurable (ω : Ω) (i j : Fin n) :
    Measurable (fun t : ℝ=>StandardFiniteIto.rowCovariance 𝓕 μ H R ω t i j) := by
  have hR (k : Fin n) : Measurable (fun t : ℝ=>R k (t.toNNReal,ω)) :=
    ((Lp.stronglyMeasurable (R k)).mono (predictable_le_product 𝓕)).measurable.comp
      (measurable_real_toNNReal.prodMk measurable_const)
  exact continuous_inner.measurable.comp ((hR i).prodMk (hR j))

variable (K : Fin n→ℝ) (hK : ∀ i,0≤K i)
variable (hR : ∀ i,∀ᵐ p ∂energyMeasure μ H,‖R i p‖^2≤K i)

include hK hR in
theorem entries_bound : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),
    ∀ i j,|StandardFiniteIto.rowCovariance 𝓕 μ H R ω t i j|≤∑ k,K k := by
  have hh : ∀ᵐ p ∂energyMeasure μ H,∀ i,‖R i p‖^2≤K i:=ae_all_iff.mpr hR
  have hs:=(Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae hh
  have hr : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),∀ i,‖R i (t.toNNReal,ω)‖^2≤K i := by
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
    rw [←timeMeasure_map H]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    simpa only [Real.toNNReal_coe,Prod.swap] using hω
  filter_upwards [hr] with ω hω
  filter_upwards [hω] with t ht i j
  have hi : K i≤∑ k,K k:=Finset.single_le_sum (fun k _=>hK k) (Finset.mem_univ i)
  have hj : K j≤∑ k,K k:=Finset.single_le_sum (fun k _=>hK k) (Finset.mem_univ j)
  have hprod : ‖R i (t.toNNReal,ω)‖*‖R j (t.toNNReal,ω)‖≤∑ k,K k := by
    nlinarith [ht i,ht j,sq_nonneg (‖R i (t.toNNReal,ω)‖-‖R j (t.toNNReal,ω)‖)]
  exact (abs_real_inner_le_norm _ _).trans hprod

include hK hR in
theorem entries_bound_window (a c : ℝ) (ha : 0≤a) (hac : a≤c) (hcH : c≤(H:ℝ)) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ∂volume.restrict (Ioc a c),
      ∀ i j,|StandardFiniteIto.rowCovariance 𝓕 μ H R ω t i j|≤∑ k,K k := by
  filter_upwards [entries_bound 𝓕 μ H R K hK hR] with ω hω
  have hs : Ioc a c⊆Ioc (0:ℝ) (H:ℝ):=fun _ ht=>⟨ha.trans_lt ht.1,ht.2.trans hcH⟩
  exact hω.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))

end SHE.FiniteItoCovarianceBounds
