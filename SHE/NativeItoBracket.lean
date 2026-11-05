module

public import SHE.PositiveGapObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The quadratic-covariation density of the actual scalar integral
rows is the native physical covariance density. The conclusion holds
on one common full-measure event, almost everywhere in time, including
all collisions among the finite observation family. -/
noncomputable section
namespace SHE.NativeItoBracket
open MeasureTheory Set PredictableL2 FiniteHaar StoppedFourier NativeObservationCovariance
open PositiveGapObservations WordRecursion CovarianceMatrix
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

def coefficient {ell M : ℝ} (f : ℝ≥0 × Ω → EllipticField ell M) (ω : Ω)
    (p : ℝ × HeatCircle) : ℝ := (CircleNormalization.push (f (p.1.toNNReal,ω)).1 p.2).re

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n → Observation)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(h:ℝ))

theorem rows_ae_real : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),∀ i : Fin n,
    rows 𝓕 μ h hell hM f hf Z hδ hgap i (t.toNNReal,ω)=
      NativeObservationEndpoint.fullIntegrand hell f (Z i).target (Z i).center (t.toNNReal,ω) := by
  have hp : ∀ᵐ p ∂energyMeasure μ h,∀ i : Fin n,
      rows 𝓕 μ h hell hM f hf Z hδ hgap i p=
        NativeObservationEndpoint.fullIntegrand hell f (Z i).target (Z i).center p :=
    ae_all_iff.mpr (fun i => NativeObservationEndpoint.process_ae 𝓕 μ h hell hM f hf _ (Z i).center)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  rw [← timeMeasure_map h]
  apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
  simpa only [Real.toNNReal_coe,Prod.swap] using hω

theorem rowCovariance_eq_density : ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),
    StandardFiniteIto.rowCovariance 𝓕 μ h (rows 𝓕 μ h hell hM f hf Z hδ hgap) ω t=
      densityMatrix (coefficient f ω) Z t := by
  filter_upwards [rows_ae_real 𝓕 μ h hell hM f hf Z hδ hgap] with ω hω
  filter_upwards [hω,ae_restrict_mem measurableSet_Ioc] with t ht htm
  have htarget (i : Fin n) : t < (Z i).target := by
    have := hgap i
    linarith [htm.2]
  ext i j
  change inner ℝ (rows 𝓕 μ h hell hM f hf Z hδ hgap i (t.toNNReal,ω))
    (rows 𝓕 μ h hell hM f hf Z hδ hgap j (t.toNNReal,ω))=
      covarianceDensity (coefficient f ω) Z t i j
  rw [ht i,ht j]
  simp only [NativeObservationEndpoint.fullIntegrand,Real.coe_toNNReal _ htm.1.le,
    ite_eq_left (htarget i),ite_eq_left (htarget j)]
  have he := row_cross_covariance hell (f (t.toNNReal,ω)) Z t i j (htarget i) (htarget j)
  simpa only [covarianceDensity,coefficient] using he

/-- Replacing a bracket density by its proved physical version does not
change the Itô formula. No continuity of the coefficient is required. -/
theorem finiteItoInput_of_density {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (h:ℝ))
    (Y : Ω → ℝ → WordRecursion.State n) (N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (hIto : PhysicalIto.FiniteItoInput μ Y
      (StandardFiniteIto.rowCovariance 𝓕 μ h (rows 𝓕 μ h hell hM f hf Z hδ hgap)) a b N) :
    PhysicalIto.FiniteItoInput μ Y (fun ω t => densityMatrix (coefficient f ω) Z t) a b N := by
  intro G dG hG
  filter_upwards [hIto G dG hG,rowCovariance_eq_density 𝓕 μ h hell hM f hf Z hδ hgap] with ω hω hΓ
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hab]
  have hs : Ioc a b ⊆ Ioc (0:ℝ) (h:ℝ) := fun t ht => ⟨ha.trans_lt ht.1,ht.2.trans hb⟩
  have hΓ' := hΓ.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  filter_upwards [hΓ'] with t ht
  rw [ht]

end SHE.NativeItoBracket
