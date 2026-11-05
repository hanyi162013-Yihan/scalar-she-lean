module

public import SHE.ScalarHeatBandCancellation
public import SHE.ScalarHeatBandJets

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.ScalarHeatBandEnvelope
open Set MeasureTheory ProbabilityTheory Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup ScalarGaussianJetScale ScalarHeatBands
open scoped NNReal ENNReal

def constant (β : ℝ) (n : ℕ) : ℝ:=2*max (ScalarGaussianJetScale.constant β n) (ScalarGaussianJetScale.constant β (n+2))
def decay (r σ s : ℝ) : ℝ:=min 1 ((σ/r^2)^(-s))

theorem constant_nonneg (β : ℝ) (n : ℕ) : 0≤constant β n:=
  mul_nonneg (by norm_num) ((ScalarGaussianJetScale.constant_nonneg β n).trans (le_max_left _ _))

theorem factor {r σ β : ℝ} (hr : 0<r) (hσ : 0<σ) (n : ℕ) :
    r^(β-(n:ℝ)-1)*(σ/r^2)^((β-(n:ℝ)-3)/2)=r^2*σ^((β-(n:ℝ)-3)/2) := by
  rw [Real.div_rpow hσ.le (sq_nonneg r),←Real.rpow_natCast_mul hr.le,div_eq_mul_inv,
    ←Real.rpow_neg hr.le]
  calc
    _=σ^((β-(n:ℝ)-3)/2)*(r^(β-(n:ℝ)-1)*r^(-((2:ℝ)*((β-(n:ℝ)-3)/2)))):=by ring
    _=r^2*σ^((β-(n:ℝ)-3)/2):=by
      rw [←Real.rpow_add hr,show β-(n:ℝ)-1+ -((2:ℝ)*((β-(n:ℝ)-3)/2))=2 by ring,Real.rpow_two]
      ring

/-- A genuine heat-band derivative has one simultaneous small-scale
and polynomial future-variance envelope. Its coefficient depends only
on the Holder exponent, Holder constant and finite derivative order. -/
theorem jet_bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ : ℝ≥0) (hσ : 0<σ)
    (j n : ℕ) (x : ℝ) :
    |iteratedDeriv (n+1) (heat σ (band a (j+1))) x|≤
      (H*constant β n)*CompactMollifier.radius (j+1)^(β-(n:ℝ)-1)*
        decay (CompactMollifier.radius (j+1)) σ (((n:ℝ)+3-β)/2) := by
  let r:=CompactMollifier.radius (j+1)
  have hr : 0<r:=CompactMollifier.radius_pos (j+1)
  have hs : 0<(σ:ℝ):=by exact_mod_cast hσ
  have hpow : 0≤r^(β-(n:ℝ)-1):=rpow_nonneg hr.le _
  have hm : 0≤max (ScalarGaussianJetScale.constant β n) (ScalarGaussianJetScale.constant β (n+2)):=
    (ScalarGaussianJetScale.constant_nonneg β n).trans (le_max_left _ _)
  have hc0 : 2*H*ScalarGaussianJetScale.constant β n≤H*constant β n:=by
    dsimp only [constant]
    nlinarith [mul_le_mul_of_nonneg_left (le_max_left (ScalarGaussianJetScale.constant β n) (ScalarGaussianJetScale.constant β (n+2))) hH]
  have hc2 : 2*H*ScalarGaussianJetScale.constant β (n+2)≤H*constant β n:=by
    dsimp only [constant]
    nlinarith [mul_le_mul_of_nonneg_left (le_max_right (ScalarGaussianJetScale.constant β n) (ScalarGaussianJetScale.constant β (n+2))) hH]
  have hsmall := (ScalarHeatBandJets.heated_positive_jet ha hH hβ hβ1 hh σ (j+1) n x).trans
    (mul_le_mul_of_nonneg_right hc0 hpow)
  have hlarge := ScalarHeatBandCancellation.jet_cancellation ha hH hβ hβ1 hh σ hσ j (n+1) x
  have hlarge' : |iteratedDeriv (n+1) (heat σ (band a (j+1))) x|≤
      (H*constant β n)*r^2*(σ:ℝ)^((β-(n:ℝ)-3)/2) := by
    have he : (β-((n+1:ℕ):ℝ)-2)/2=(β-(n:ℝ)-3)/2:=by push_cast; ring
    rw [he] at hlarge
    exact hlarge.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc2 (sq_nonneg r)) (rpow_nonneg hs.le _))
  have hfactor := factor (β:=β) hr hs n
  have he : (β-(n:ℝ)-3)/2= -(((n:ℝ)+3-β)/2):=by ring
  rw [he] at hfactor hlarge'
  have hlarge'' : |iteratedDeriv (n+1) (heat σ (band a (j+1))) x|≤
      ((H*constant β n)*r^(β-(n:ℝ)-1))*((σ:ℝ)/r^2)^(-(((n:ℝ)+3-β)/2)) := by
    rw [mul_assoc,hfactor,←mul_assoc]
    exact hlarge'
  have hmin:=le_min hsmall hlarge''
  have hA : 0≤(H*constant β n)*r^(β-(n:ℝ)-1):=
    mul_nonneg (mul_nonneg hH (constant_nonneg β n)) hpow
  change _≤((H*constant β n)*r^(β-(n:ℝ)-1))*min 1 (((σ:ℝ)/r^2)^(-(((n:ℝ)+3-β)/2)))
  rw [mul_min_of_nonneg _ _ hA,mul_one]
  exact hmin

end SHE.ScalarHeatBandEnvelope
