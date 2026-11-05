module

public import SHEStochastic.MatrixProfileDisplacement
public import SHEStochastic.MatrixHeatCovarianceL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixProfileStability
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance MatrixProfileUpdate
  MatrixProfileFixedPoint SHE.ProfileVariance SHE.ProfileL2 SHE.StoppedFourier
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (G : Coefficient (Fin n))

def meanConstant (K β : ℝ) : ℝ :=
  (2*(G.bound : ℝ)*K)*GaussianNormMoment.moment (Fin n) (β+1)*(lowerConstant*G.lower)^((β-1)/2)

def varianceConstant (K β : ℝ) : ℝ :=
  (2*(G.bound : ℝ)*K)*SHE.GaussianAudit.secondScoreAbsIncrementMoment β*
    (lowerConstant*G.lower)^(β/2-1)*SHE.GaussianSignedCovariance.covarianceBoundConstant n

def memoryConstant (K β : ℝ) : ℝ := (1+heatConstant)*varianceConstant G K β

theorem meanConstant_nonneg {K β : ℝ} (hK : 0 ≤ K) : 0 ≤ meanConstant G K β :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)
    (GaussianNormMoment.nonneg _)) (Real.rpow_nonneg (mul_nonneg lowerConstant_pos.le G.lower_pos.le) _)

theorem varianceConstant_nonneg {K β : ℝ} (hK : 0 ≤ K) : 0 ≤ varianceConstant G K β :=
  mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) G.bound.coe_nonneg) hK)
    (SHE.GaussianProfile.incrementMoment_nonneg _))
    (Real.rpow_nonneg (mul_nonneg lowerConstant_pos.le G.lower_pos.le) _))
    (SHE.GaussianSignedCovariance.covarianceBoundConstant_nonneg n)

theorem memoryConstant_nonneg {K β : ℝ} (hK : 0 ≤ K) : 0 ≤ memoryConstant G K β :=
  mul_nonneg (by linarith [heatConstant_pos]) (varianceConstant_nonneg G hK)

theorem floor_power {r : ℝ} (hr : 0 ≤ r) (q : ℝ) :
    (lowerConstant*G.lower*r^(1/2 : ℝ))^q = (lowerConstant*G.lower)^q*r^(q/2) := by
  rw [Real.mul_rpow (mul_nonneg lowerConstant_pos.le G.lower_pos.le) (Real.rpow_nonneg hr _),
    ← Real.rpow_mul hr]
  congr 2
  ring

theorem two_inputs {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (φ ψ : Domain → EuclideanSpace ℝ (Fin n))
    (κ η : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (hκS : ∀ p, κ p ∈ constraint G) (hηS : ∀ p, η p ∈ constraint G)
    (p : HeatCovarianceMeasure.Window × SpatialCircle) :
    ‖update G φ κ p-update G ψ η p‖ ≤
      meanConstant G K β*p.1.val^((β-1)/4)*‖φ (p.1.val,p.2)-ψ (p.1.val,p.2)‖+
      varianceConstant G K β*p.1.val^((β-2)/4)*‖covariance κ p-covariance η p‖ := by
  have hlo : 0 < lowerConstant*G.lower*p.1.val^(1/2 : ℝ) :=
    mul_pos (mul_pos lowerConstant_pos G.lower_pos) (Real.rpow_pos_of_pos p.1.property.1 _)
  have hlκ := lower_bound κ hκ (upper G) G.lower (upper G) G.lower_pos.le
    (fun z => (hκS z).2) (fun z => (hκS z).1.1) (fun z => (hκS z).1.2) p
  have hlη := lower_bound η hη (upper G) G.lower (upper G) G.lower_pos.le
    (fun z => (hηS z).2) (fun z => (hηS z).1.1) (fun z => (hηS z).1.2) p
  have hm := MatrixGaussianAverage.mean_lipschitz G hlo hK hβ hG (covariance κ p) hlκ
    (φ (p.1.val,p.2)) (ψ (p.1.val,p.2))
  have hv := MatrixGaussianAverage.covariance_lipschitz G hlo hK hβ hG
    (covariance κ p) (covariance η p) hlκ hlη (ψ (p.1.val,p.2))
  rw [floor_power G p.1.property.1.le] at hm hv
  have hpow1 : ((β-1)/2)/2=(β-1)/4 := by ring
  have hpow2 : (β/2-1)/2=(β-2)/4 := by ring
  rw [hpow1] at hm
  rw [hpow2] at hv
  apply (norm_sub_le_norm_sub_add_norm_sub (update G φ κ p) (update G ψ κ p) (update G ψ η p)).trans
  dsimp only [update,meanConstant,varianceConstant]
  convert add_le_add hm hv using 1 <;> ring

theorem l2_volterra {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (φ ψ : Domain → EuclideanSpace ℝ (Fin n))
    (κ η : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (hκS : ∀ p, κ p ∈ constraint G) (hηS : ∀ p, η p ∈ constraint G)
    (r : HeatCovarianceMeasure.Window)
    (hmean : MemLp (fun x => ‖φ (r.val,x)-ψ (r.val,x)‖) 2 AddCircle.haarAddCircle)
    (hκfix : ∀ x, κ (r.val,x)=update G φ κ (r,x))
    (hηfix : ∀ x, η (r.val,x)=update G ψ η (r,x)) :
    normTwo AddCircle.haarAddCircle (fun x => ‖κ (r.val,x)-η (r.val,x)‖) ≤
      meanConstant G K β*r.val^((β-1)/4)*
        normTwo AddCircle.haarAddCircle (fun x => ‖φ (r.val,x)-ψ (r.val,x)‖)+
      memoryConstant G K β*r.val^((β-2)/4)*
        (∫ s in (0 : ℝ)..r.val, (r.val-s)^(-(1/2 : ℝ))*
          normTwo AddCircle.haarAddCircle (fun y => ‖κ (s,y)-η (s,y)‖)) := by
  have hM : 0 ≤ upper G := by unfold upper; positivity
  have hκM (p : Domain) : ‖κ p‖ ≤ upper G := (hκS p).2
  have hηM (p : Domain) : ‖η p‖ ≤ upper G := (hηS p).2
  have hdiff (p : Domain) : ‖κ p-η p‖ ≤ 2*upper G :=
    (norm_sub_le _ _).trans (by linarith [hκM p,hηM p])
  have ht : MemLp (fun x => ‖κ (r.val,x)-η (r.val,x)‖) 2 AddCircle.haarAddCircle :=
    bounded_memLp (((hκ.sub hη).norm).comp (measurable_const.prodMk measurable_id))
      (fun x => by rw [abs_of_nonneg (norm_nonneg _)]; exact hdiff (r.val,x))
  have hcm := (MatrixHeatCovarianceL2.measurable κ hκ (upper G) hκM r).sub
    (MatrixHeatCovarianceL2.measurable η hη (upper G) hηM r)
  have hV : MemLp (fun x => ‖covariance κ (r,x)-covariance η (r,x)‖) 2 AddCircle.haarAddCircle := by
    apply bounded_memLp (C := upperConstant*(2*upper G)*r.val^(1/2 : ℝ)) hcm.norm
    intro x
    rw [abs_of_nonneg (norm_nonneg _)]
    exact difference κ η hκ hη (upper G) (2*upper G) (by positivity) hκM hηM hdiff (r,x)
  have hA : 0 ≤ meanConstant G K β*r.val^((β-1)/4) :=
    mul_nonneg (meanConstant_nonneg G hK) (Real.rpow_nonneg r.property.1.le _)
  have hB : 0 ≤ varianceConstant G K β*r.val^((β-2)/4) :=
    mul_nonneg (varianceConstant_nonneg G hK) (Real.rpow_nonneg r.property.1.le _)
  have hb := normTwo_sum_bound ht hmean hV hA hB (fun x => by
    simp only [abs_of_nonneg (norm_nonneg _)]
    rw [hκfix x,hηfix x]
    exact two_inputs G hK hβ hG φ ψ κ η hκ hη hκS hηS (r,x))
  have htransfer := MatrixHeatCovarianceL2.bound κ η hκ hη (upper G) hM hκM hηM r
  apply hb.trans
  exact add_le_add le_rfl
    ((mul_le_mul_of_nonneg_left htransfer hB).trans_eq (by unfold memoryConstant; ring))

/-- One-input L2 stability for exact coupled profiles, obtained from
the already proved scalar Volterra absorption theorem. -/
theorem l2_stability {K β h D : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hD : 0 ≤ D)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (φ ψ : Domain → EuclideanSpace ℝ (Fin n))
    (κ η : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (hκS : ∀ p, κ p ∈ constraint G) (hηS : ∀ p, η p ∈ constraint G)
    (hmean : ∀ r ∈ Ioc 0 h,
      MemLp (fun x => ‖φ (r,x)-ψ (r,x)‖) 2 AddCircle.haarAddCircle ∧
        normTwo AddCircle.haarAddCircle (fun x => ‖φ (r,x)-ψ (r,x)‖) ≤ D)
    (hsmall : memoryConstant G K β*SHE.ProfileVolterra.powerConstant ((β-1)/4)*h^(β/4) ≤ 1/2)
    (hκfix : ∀ r (hr : r ∈ Ioc 0 h) x,
      κ (r,x)=update G φ κ (⟨r,hr.1,hr.2.trans hh1⟩,x))
    (hηfix : ∀ r (hr : r ∈ Ioc 0 h) x,
      η (r,x)=update G ψ η (⟨r,hr.1,hr.2.trans hh1⟩,x)) :
    ∀ r ∈ Ioc 0 h,
      normTwo AddCircle.haarAddCircle (fun x => ‖κ (r,x)-η (r,x)‖) ≤
        2*(meanConstant G K β*D)*r^((β-1)/4) ∧
      IntervalIntegrable (fun s => (r-s)^(-(1/2 : ℝ))*
        normTwo AddCircle.haarAddCircle (fun y => ‖κ (s,y)-η (s,y)‖)) volume 0 r ∧
      (∫ s in (0 : ℝ)..r, (r-s)^(-(1/2 : ℝ))*
        normTwo AddCircle.haarAddCircle (fun y => ‖κ (s,y)-η (s,y)‖)) ≤
        2*(meanConstant G K β*D)*SHE.ProfileVolterra.powerConstant ((β-1)/4)*r^((β+1)/4) := by
  let f : ℝ → ℝ := fun r => normTwo AddCircle.haarAddCircle (fun y => ‖κ (r,y)-η (r,y)‖)
  have hf : Measurable f := spatial_normTwo_measurable (hκ.sub hη).norm
  have hM : 0 ≤ upper G := by unfold upper; positivity
  have hfb : ∀ r ∈ Ioc 0 h, f r ≤ 2*upper G := by
    intro r hr
    apply normTwo_bound (((hκ.sub hη).norm).comp (measurable_const.prodMk measurable_id)) (by positivity)
    intro x
    change |‖κ (r,x)-η (r,x)‖| ≤ 2*upper G
    rw [abs_of_nonneg (norm_nonneg _)]
    have hκM : ‖κ (r,x)‖ ≤ upper G := (hκS _).2
    have hηM : ‖η (r,x)‖ ≤ upper G := (hηS _).2
    exact (norm_sub_le _ _).trans (by linarith)
  have hvol : ∀ r ∈ Ioc 0 h, f r ≤ (meanConstant G K β*D)*r^((β-1)/4)+
      memoryConstant G K β*r^((β-2)/4)*
        (∫ s in (0 : ℝ)..r, (r-s)^(-(1/2 : ℝ))*f s) := by
    intro r hr
    have he := l2_volterra G hK hβ.le hG φ ψ κ η hκ hη hκS hηS
      ⟨r,hr.1,hr.2.trans hh1⟩ (hmean r hr).1 (hκfix r hr) (hηfix r hr)
    have hm := mul_le_mul_of_nonneg_left (hmean r hr).2
      (mul_nonneg (meanConstant_nonneg G (β := β) hK) (Real.rpow_nonneg hr.1.le ((β-1)/4)))
    apply he.trans
    exact (add_le_add hm le_rfl).trans_eq (by ring)
  exact SHE.ProfileVolterra.profile_volterra_stability hβ hβ1 hh hh1
    (mul_nonneg (meanConstant_nonneg G hK) hD) (memoryConstant_nonneg G hK)
    (by positivity : 0 ≤ 2*upper G) hf (fun _ _ => normTwo_nonneg _ _) hfb hsmall hvol

theorem exists_stability_horizon {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ memoryConstant G K β*
      SHE.ProfileVolterra.powerConstant ((β-1)/4)*h^(β/4) ≤ 1/2 :=
  SHE.ProfileVolterra.exists_absorption_horizon (by linarith)
    (memoryConstant_nonneg G hK) (by positivity)

end SHEStochastic.MatrixProfileStability
