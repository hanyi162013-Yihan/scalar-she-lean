module

public import SHE.ScoreProjectionEnergy
public import SHE.FullResidualFrameRange
public import SHE.HolderGeneralScoreInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SHE.StoppedInactiveCoordinate
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement GaussianCoordinates MeasurableGaussianScores
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {n : ℕ} (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)

theorem row_tail (q T : ℝ) (x : HeatCircle) (p : Domain) :
    projection (Fin.succ : Fin n→Fin (n+1)) (stoppedRow (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) p)=
      stoppedRow σ target center p := by ext i; rfl

theorem covariance_tail (q T : ℝ) (x : HeatCircle) (c : Domain→ℝ) :
    (stoppedCovariance (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) c q).submatrix
      (Fin.succ : Fin n→Fin (n+1)) Fin.succ=stoppedCovariance σ target center c q := by
  ext i j
  rfl

theorem row_head (q T : ℝ) (x : HeatCircle) (p : Domain) (hp : q≤p.1) :
    stoppedRow (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) p 0=0 := by
  simp only [stoppedRow,Fin.cons_zero,not_lt.mpr hp,ite_false]

theorem covariance_head (q T : ℝ) (x : HeatCircle) (c : Domain→ℝ) (j : Fin (n+1)) :
    stoppedCovariance (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) c q j 0=0 := by
  apply integral_eq_zero_of_ae
  have ht : ∀ᵐ p : Domain ∂historyMeasure q,q≤p.1:=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  filter_upwards [ht] with p hp
  change c p*stoppedRow (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) p j*
    stoppedRow (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) p 0=0
  rw [row_head σ target center q T x p hp,mul_zero]

/-- At the true newest endpoint sigma=q its future coordinate is zero.
Deleting this coordinate leaves the EXACT singular Gaussian score energy,
so no artificial positive heat gap is needed for input-energy transfer. -/
theorem score_ae (hages : ∀ i,σ i≤target i) (q T : ℝ) (hT : q≤T) (x : HeatCircle)
    (c : Domain→ℝ) (hc : Measurable c) {ell U : ℝ} (hell : 0<ell)
    (hb : ∀ p,ell≤c p ∧ c p≤U) :
    ∀ᵐ p ∂historyMeasure q,
      scoreVariance (stoppedCovariance (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) c q)
        (stoppedRow (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) p)=
      scoreVariance (stoppedCovariance σ target center c q) (stoppedRow σ target center p) := by
  let A:=stoppedCovariance (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) c q
  have hfull : ∀ i,(Fin.cons q σ : Fin (n+1)→ℝ) i≤(Fin.cons T target : Fin (n+1)→ℝ) i :=
    Fin.cases hT hages
  have hA : A.PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef _ _ _ hfull q hc
    (fun p=>⟨hell.le.trans (hb p).1,(hb p).2⟩)
  have hr:=FullResidualFrameRange.row_mem_all_ranges_ae (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center)
    hfull q (fun _ : Unit=>c) (fun _=>hc) hell (fun _=>hb)
  have ht : ∀ᵐ p : Domain ∂historyMeasure q,q≤p.1:=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  have hzero (i : Fin (n+1)) (hi : i∉Set.range (Fin.succ : Fin n→Fin (n+1))) (j : Fin (n+1)) : A j i=0 := by
    have hi0 : i=0:=by
      revert hi
      refine Fin.cases ?_ (fun a=>?_) i
      · intro _; rfl
      · intro ha; exact False.elim (ha ⟨a,rfl⟩)
    rw [hi0]
    exact covariance_head σ target center q T x c j
  filter_upwards [hr,ht] with p hp hpt
  have hdz (i : Fin (n+1)) (hi : i∉Set.range (Fin.succ : Fin n→Fin (n+1))) :
      stoppedRow (Fin.cons q σ) (Fin.cons T target) (Fin.cons x center) p i=0 := by
    revert hi
    refine Fin.cases ?_ (fun a=>?_) i
    · intro _; exact row_head σ target center q T x p hpt
    · intro ha; exact False.elim (ha ⟨a,rfl⟩)
  have hh:=ScoreProjectionEnergy.scoreVariance_projection (Fin.succ : Fin n→Fin (n+1))
    (Fin.succ_injective n) hA hzero (hp ()) hdz
  simpa only [A,covariance_tail,row_tail] using hh

end SHE.StoppedInactiveCoordinate
