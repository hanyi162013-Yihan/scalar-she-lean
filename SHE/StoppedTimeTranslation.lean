module

public import SHE.StoppedScoreL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.StoppedTimeTranslation
open Set MeasureTheory AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 MeasurableGaussianScores
local instance stoppedTimeTranslation_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def shift (q : ℝ) : Domain ≃ᵐ Domain :=
  (MeasurableEquiv.addLeft q).prodCongr (MeasurableEquiv.refl HeatCircle)

theorem shift_apply (q : ℝ) (p : Domain) : shift q p=(q+p.1,p.2) := rfl

theorem shift_preserving (q : ℝ) :
    MeasurePreserving (shift q) (historyMeasure 0) (historyMeasure q) := by
  have ht : MeasurePreserving (fun t : ℝ=>q+t)
      (volume.restrict (Ici (0:ℝ))) (volume.restrict (Ici q)) := by
    have hpre : (fun t : ℝ=>q+t) ⁻¹' Ici q=Ici 0 := by
      ext t
      simp only [Set.mem_preimage,Set.mem_Ici]
      constructor <;> intro h <;> linarith
    simpa only [hpre] using
      (measurePreserving_add_left volume q).restrict_preimage (s:=Ici q) measurableSet_Ici
  exact ht.prod (MeasurePreserving.id haarAddCircle)

theorem row_shift (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (q : ℝ) (p : Domain) :
    stoppedRow σ target center (shift q p)=
      stoppedRow (fun i=>σ i-q) (fun i=>target i-q) center p := by
  apply (WithLp.equiv 2 (Fin n→ℝ)).injective
  funext i
  change (if q+p.1<σ i then (ProfileVariance.heatPhysical (target i-(q+p.1)) (center i) p.2).re else 0)=
    (if p.1<σ i-q then (ProfileVariance.heatPhysical ((target i-q)-p.1) (center i) p.2).re else 0)
  rw [show target i-(q+p.1)=(target i-q)-p.1 by ring]
  have hiff : (q+p.1<σ i)↔(p.1<σ i-q) := by constructor <;> intro h <;> linarith
  simp only [hiff]

/-- The entire individually stopped covariance, with every distinct
stop and target retained, is exactly its relative-time covariance. -/
theorem covariance_shift (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (c : Domain→ℝ) (q : ℝ) :
    stoppedCovariance σ target center c q=
      stoppedCovariance (fun i=>σ i-q) (fun i=>target i-q) center
        (fun p=>c (shift q p)) 0 := by
  ext i j
  have he := (shift_preserving q).integral_comp'
    (fun p : Domain=>c p*stoppedRow σ target center p i*stoppedRow σ target center p j)
  change (∫ p,c p*stoppedRow σ target center p i*stoppedRow σ target center p j ∂historyMeasure q)=_
  rw [←he]
  apply integral_congr_ae
  exact ae_of_all _ (fun p=>by dsimp only;rw [row_shift])

theorem score_input_shift (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (c e : Domain→ℝ) (q : ℝ) :
    (fun x : HeatCircle=>∫ p,|e p| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x) c q)
      (stoppedRow σ target (fun i=>center i+x) p) ∂historyMeasure q)=
    StoppedScoreLeverage.scoreInput (fun i=>σ i-q) (fun i=>target i-q) center
      (fun p=>c (shift q p)) (fun p=>e (shift q p)) := by
  funext x
  have he := (shift_preserving q).integral_comp'
    (fun p : Domain=>|e p| *scoreVariance
      (stoppedCovariance σ target (fun i=>center i+x) c q)
      (stoppedRow σ target (fun i=>center i+x) p))
  rw [←he,covariance_shift]
  apply integral_congr_ae
  exact ae_of_all _ (fun p=>by dsimp only;rw [row_shift])

end SHE.StoppedTimeTranslation
