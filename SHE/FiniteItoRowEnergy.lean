module

public import SHE.FiniteItoCovarianceBounds
public import SHE.ProcessEnergy
public import SHE.PredictableTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.FiniteItoRowEnergy
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable {n : ℕ} (R : Fin n→Process (E:=C) 𝓕 μ H)

def density (ω : Ω) (t : ℝ) : ℝ:=∑ i:Fin n,‖R i (t.toNNReal,ω)‖^2

theorem density_nonneg (ω : Ω) (t : ℝ) : 0≤density 𝓕 μ H R ω t:=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

/-- Genuine predictable L² rows have an integrable pathwise covariance
majorant, without a uniform-in-time bounded-row hypothesis. -/
theorem density_integrable (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hbH : b≤(H:ℝ)) :
    ∀ᵐ ω∂μ,IntegrableOn (density 𝓕 μ H R ω) (Ioc a b) volume := by
  have he (i:Fin n) : ∀ᵐ ω∂μ,Integrable (fun t:ℝ≥0=>‖R i (t,ω)‖^2) (timeMeasure H) := by
    have hi:= (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp (R i))).norm.integrable_sq
    exact hi.prod_left_ae
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply integrable_finsetSum
  intro i _
  have hp:=((timeMeasurePreserving H).integrable_comp_emb (g:=fun t:ℝ=>‖R i (t.toNNReal,ω)‖^2) nonnegative_coe_measurableEmbedding).1 (by simpa only [Function.comp_def,Real.toNNReal_coe] using hω i)
  exact hp.mono_measure (Measure.restrict_mono_set volume (fun t ht=>⟨ha.trans_lt ht.1,ht.2.trans hbH⟩))

theorem entry_bound (ω : Ω) (t : ℝ) (i j : Fin n) :
    |StandardFiniteIto.rowCovariance 𝓕 μ H R ω t i j|≤density 𝓕 μ H R ω t := by
  have hi : ‖R i (t.toNNReal,ω)‖^2≤density 𝓕 μ H R ω t:=
    by
      change ‖R i (t.toNNReal,ω)‖^2≤∑ k:Fin n,‖R k (t.toNNReal,ω)‖^2
      exact Finset.single_le_sum (fun k _=>sq_nonneg ‖R k (t.toNNReal,ω)‖) (Finset.mem_univ i)
  have hj : ‖R j (t.toNNReal,ω)‖^2≤density 𝓕 μ H R ω t:=
    by
      change ‖R j (t.toNNReal,ω)‖^2≤∑ k:Fin n,‖R k (t.toNNReal,ω)‖^2
      exact Finset.single_le_sum (fun k _=>sq_nonneg ‖R k (t.toNNReal,ω)‖) (Finset.mem_univ j)
  apply (abs_real_inner_le_norm _ _).trans
  nlinarith [sq_nonneg (‖R i (t.toNNReal,ω)‖-‖R j (t.toNNReal,ω)‖)]

end SHE.FiniteItoRowEnergy
