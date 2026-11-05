module

public import SHE.NativeJointBracketDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.NativeJointCovariance
open MeasureTheory Set GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open NativeJointPhysicalRows NativeJointBracketDefect
open scoped NNReal ENNReal
local instance nativeJointCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

theorem rows_ae_real (hΛ : 0≤Λ) (b : ℝ≥0) (hgap : ∀ i,(b:ℝ)<(Z i).target) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t<(b:ℝ) → ∀ i,
      NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap hΛ i (t.toNNReal,ω)=
        physicalRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z (t.toNNReal,ω) i := by
  have hp := NativeJointPhysicalRows.rows_ae 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z hΛ b hgap
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  rw [← timeMeasure_map H]
  apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hω] with t ht
  intro htb i
  have hh := ht (by exact_mod_cast htb) i
  simpa only [Prod.swap,Real.toNNReal_coe] using hh

theorem rowCovariance_eq_physicalGram (hΛ : 0≤Λ) (b : ℝ≥0) (hgap : ∀ i,(b:ℝ)<(Z i).target) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t<(b:ℝ) →
      StandardFiniteIto.rowCovariance 𝓕 μ H
        (NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap hΛ) ω t=
      physicalGram 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z (t.toNNReal,ω) := by
  filter_upwards [rows_ae_real 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z hΛ b hgap] with ω hω
  filter_upwards [hω] with t ht htb
  ext i j
  change inner ℝ
    (NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap hΛ i (t.toNNReal,ω))
    (NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap hΛ j (t.toNNReal,ω))=_
  rw [ht htb i,ht htb j]
  rfl

/-- The actual joint bracket is local TOTAL variance kappa+a(V) plus
the literal first-defect matrix. This is derived from the actual common
Haar analysis rows and the scalar coefficient representative. -/
theorem rowCovariance_eq_total_add_defect (hΛ : 0≤Λ) (b : ℝ≥0)
    {δ : ℝ} (hδ : 0<δ) (hgap : ∀ i,δ≤(Z i).target-(b:ℝ)) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (H:ℝ)),t<(b:ℝ) →
      StandardFiniteIto.rowCovariance 𝓕 μ H
        (NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b
          (fun i => by have := hgap i;linarith) hΛ) ω t=
      CovarianceMatrix.densityMatrix
        (fun tx => κ+a (PredictableScalarField.wordField (Function.uncurry S.second) ω tx)) Z t+
      defect 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z (t.toNNReal,ω) := by
  have hstrict : ∀ i,(b:ℝ)<(Z i).target := by intro i;have := hgap i;linarith
  filter_upwards [rowCovariance_eq_physicalGram 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z hΛ b hstrict] with ω hω
  filter_upwards [hω,ae_restrict_mem measurableSet_Ioc] with t ht htm htb
  rw [ht htb,physicalGram_eq_base_add_defect]
  have he := baseGram_eq_total_density 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z hδ hgap
    (t.toNNReal,ω) (by rw [Real.coe_toNNReal _ htm.1.le];exact htb.le)
  simp only [Real.coe_toNNReal _ htm.1.le] at he
  rw [he]

end SHE.NativeJointCovariance
