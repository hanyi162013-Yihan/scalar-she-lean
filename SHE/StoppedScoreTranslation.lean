module

public import SHE.StoppedScoreLeverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.StoppedScoreLeverage
open Set MeasureTheory AddCircle Finset StoppedFourier StoppedGaussianFeatures GaussianAudit
  GaussianGramScore GaussianIncrement MeasurableGaussianScores ProfileVariance
open scoped InnerProductSpace
local instance stoppedScoreTranslation_periodPos : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

def domainTranslate (x : HeatCircle) : Domain ≃ᵐ Domain :=
  (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.addRight x)

theorem domainTranslate_apply (x : HeatCircle) (p : Domain) :
    domainTranslate x p = (p.1,p.2+x) := rfl

theorem domainTranslate_preserving (x : HeatCircle) (q : ℝ) :
    MeasurePreserving (domainTranslate x) (historyMeasure q) (historyMeasure q) := by
  change MeasurePreserving (Prod.map id (fun y : HeatCircle => y+x)) _ _
  exact (MeasurePreserving.id (volume.restrict (Ici q))).prod (measurePreserving_add_right haarAddCircle x)

theorem heatPhysical_translate (t : ℝ) (a y x : HeatCircle) :
    heatPhysical t (a+x) (y+x) = heatPhysical t a y := by
  simpa only [physicalCircleHeat_eq] using GaussianAudit.physicalCircleHeat_translate t a y x

/-- All original stopping masks are retained under physical circle
translation; the coefficient profile is translated by the same amount. -/
theorem stoppedRow_translate (x : HeatCircle) (p : Domain) :
    stoppedRow σ target (fun i => center i+x) (domainTranslate x p) =
      stoppedRow σ target center p := by
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change (if p.1 < σ i then (heatPhysical (target i-p.1) (center i+x) (p.2+x)).re else 0) =
    (if p.1 < σ i then (heatPhysical (target i-p.1) (center i) p.2).re else 0)
  rw [heatPhysical_translate]

theorem stoppedCovariance_translate (x : HeatCircle) (c : Domain → ℝ) (q : ℝ) :
    StoppedGaussianFeatures.stoppedCovariance σ target (fun i => center i+x) c q =
      StoppedGaussianFeatures.stoppedCovariance σ target center (fun p => c (domainTranslate x p)) q := by
  ext i j
  have he := (domainTranslate_preserving x q).integral_comp'
    (fun p : Domain => c p*stoppedRow σ target (fun i => center i+x) p i*
      stoppedRow σ target (fun i => center i+x) p j)
  change (∫ p,c p*stoppedRow σ target (fun i => center i+x) p i*
    stoppedRow σ target (fun i => center i+x) p j ∂historyMeasure q) = _
  rw [← he]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by dsimp only; rw [stoppedRow_translate])

/-- The actual covariance mark, after the exact physical change of
variables. The reference kernel can therefore remain independent of
the coefficient profile and of the output center. -/
theorem score_integral_translate (x : HeatCircle) (c e : Domain → ℝ) (q : ℝ) :
    (∫ p,|e p| * scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target (fun i => center i+x) c q)
      (stoppedRow σ target (fun i => center i+x) p) ∂historyMeasure q) =
    ∫ p,|e (domainTranslate x p)| * scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target center (fun p => c (domainTranslate x p)) q)
      (stoppedRow σ target center p) ∂historyMeasure q := by
  have he := (domainTranslate_preserving x q).integral_comp'
    (fun p : Domain => |e p| * scoreVariance
      (StoppedGaussianFeatures.stoppedCovariance σ target (fun i => center i+x) c q)
      (stoppedRow σ target (fun i => center i+x) p))
  rw [← he,stoppedCovariance_translate]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by dsimp only; rw [stoppedRow_translate])

theorem translated_score_le_reference_ae (hages : ∀ i,σ i ≤ target i)
    (x : HeatCircle) (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p,0 ≤ c p ∧ c p ≤ M) {ell : ℝ} (hell : 0 < ell)
    (hcl : ∀ p,ell ≤ c p) (q : ℝ) :
    ∀ᵐ p ∂historyMeasure q,
      scoreVariance (StoppedGaussianFeatures.stoppedCovariance σ target (fun i => center i+x) c q)
        (stoppedRow σ target (fun i => center i+x) (domainTranslate x p)) ≤
          referenceKernel σ target center hages q p/ell := by
  rw [stoppedCovariance_translate]
  simp_rw [stoppedRow_translate]
  exact score_le_reference_ae σ target center hages (fun p => c (domainTranslate x p))
    (hc.comp (domainTranslate x).measurable) M (fun p => hcb _) hell (fun p => hcl _) q

end SHE.StoppedScoreLeverage
