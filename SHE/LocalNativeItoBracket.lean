module

public import SHE.LocalNativeObservations
public import SHE.NativeItoBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.LocalNativeItoBracket
open MeasureTheory Set PredictableL2 FiniteHaar StoppedFourier NativeObservationCovariance
open LocalNativeObservations WordRecursion CovarianceMatrix
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n → Observation) (b : ℝ≥0)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(b:ℝ))

theorem rows_ae_real : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),∀ i : Fin n,
    rows 𝓕 μ h hell hM f hf Z b hδ hgap i (t.toNNReal,ω)=
      NativeObservationProcess.integrand hell f (Z i).target b (Z i).center (t.toNNReal,ω) := by
  have hp : ∀ᵐ p ∂energyMeasure μ h,∀ i : Fin n,
      rows 𝓕 μ h hell hM f hf Z b hδ hgap i p=
        NativeObservationProcess.integrand hell f (Z i).target b (Z i).center p :=
    ae_all_iff.mpr (fun i => NativeObservationProcess.process_ae 𝓕 μ h hell hM f hf _ (Z i).center)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  rw [← timeMeasure_map h]
  apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
  simpa only [Real.toNNReal_coe,Prod.swap] using hω

/-- True local-window bracket density. A target may lie below global h;
the upper endpoint b is discarded only as a Lebesgue-null singleton. -/
theorem rowCovariance_eq_density (hbh : b ≤ h) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (b:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ h (rows 𝓕 μ h hell hM f hf Z b hδ hgap) ω t=
        densityMatrix (NativeItoBracket.coefficient f ω) Z t := by
  filter_upwards [rows_ae_real 𝓕 μ h hell hM f hf Z b hδ hgap] with ω hω
  have hsub : Ioc (0:ℝ) (b:ℝ) ⊆ Ioc (0:ℝ) (h:ℝ) := by
    intro t ht
    exact ⟨ht.1,ht.2.trans (by exact_mod_cast hbh)⟩
  have hr := hω.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  filter_upwards [hr,ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht htm hne
  have htb : t < (b:ℝ) := lt_of_le_of_ne htm.2 hne
  have htarget (i : Fin n) : (b:ℝ) < (Z i).target := by have := hgap i; linarith
  ext i j
  change inner ℝ (rows 𝓕 μ h hell hM f hf Z b hδ hgap i (t.toNNReal,ω))
    (rows 𝓕 μ h hell hM f hf Z b hδ hgap j (t.toNNReal,ω))=
      covarianceDensity (NativeItoBracket.coefficient f ω) Z t i j
  rw [ht i,ht j,NativeObservationProcess.integrand_eq hell f (htarget i),
    NativeObservationProcess.integrand_eq hell f (htarget j)]
  simp only [Real.coe_toNNReal _ htm.1.le,ite_eq_left htb]
  have he := row_cross_covariance hell (f (t.toNNReal,ω)) Z t i j
    (htb.trans (htarget i)) (htb.trans (htarget j))
  simpa only [covarianceDensity,NativeItoBracket.coefficient] using he

theorem finiteItoInput_of_density (hbh : b ≤ h) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ (b:ℝ))
    (Y : Ω → ℝ → WordRecursion.State n) (N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (hIto : PhysicalIto.FiniteItoInput μ Y
      (StandardFiniteIto.rowCovariance 𝓕 μ h (rows 𝓕 μ h hell hM f hf Z b hδ hgap)) a b N) :
    PhysicalIto.FiniteItoInput μ Y (fun ω t => densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b N := by
  intro G dG hG
  filter_upwards [hIto G dG hG,rowCovariance_eq_density 𝓕 μ h hell hM f hf Z b hδ hgap hbh] with ω hω hΓ
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  have hs : Ioc a (b:ℝ) ⊆ Ioc (0:ℝ) (b:ℝ) := fun t ht => ⟨ha.trans_lt ht.1,ht.2⟩
  have hΓ' := hΓ.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  filter_upwards [hΓ'] with t ht
  rw [ht]

end SHE.LocalNativeItoBracket
