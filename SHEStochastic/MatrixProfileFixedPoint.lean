module

public import SHEStochastic.MatrixProfileUpdate
public import SHEStochastic.BoundedMeasurableFixedPoint
public import SHE.ProfileVolterra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixProfileFixedPoint
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance MatrixProfileUpdate
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ} (G : Coefficient (Fin n))

def upper : ℝ := (G.bound : ℝ)^2+1

def constraint : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Icc (G.lower • 1) (upper G • 1) ∩ {A | ‖A‖ ≤ upper G}

theorem constraint_closed : IsClosed (constraint G) :=
  isClosed_Icc.inter (isClosed_le continuous_norm continuous_const)

theorem baseline_mem : G.covariance 0 ∈ constraint G :=
  ⟨⟨G.lower_bound 0,G.covariance_upper 0⟩,
    (G.covariance_bound 0).trans (le_add_of_nonneg_right zero_le_one)⟩

def extension (h : ℝ) (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (p : Domain) :=
  if p.1 ∈ Ioc 0 h then κ p else G.covariance 0

theorem extension_measurable {h : ℝ} {κ : Domain → Matrix (Fin n) (Fin n) ℝ}
    (hκ : Measurable κ) : Measurable (extension G h κ) :=
  hκ.ite (measurableSet_Ioc.preimage measurable_fst) measurable_const

theorem extension_mem {h : ℝ} {κ : Domain → Matrix (Fin n) (Fin n) ℝ}
    (hκ : ∀ p, κ p ∈ constraint G) (p : Domain) : extension G h κ p ∈ constraint G := by
  unfold extension
  split_ifs
  · exact hκ p
  · exact baseline_mem G

theorem update_extension (φ : Domain → EuclideanSpace ℝ (Fin n))
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) {h : ℝ}
    (p : HeatCovarianceMeasure.Window × SpatialCircle) (hp : p.1.val ≤ h) :
    update G φ (extension G h κ) p = update G φ κ p := by
  unfold update covariance
  congr 1
  apply HeatCovarianceMeasure.integral_congr_time
  intro s hs y
  exact if_pos ⟨hs.1,hs.2.le.trans hp⟩

def canonicalUpdate (φ : Domain → EuclideanSpace ℝ (Fin n)) {h : ℝ} (hh1 : h ≤ 1)
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (p : Domain) : Matrix (Fin n) (Fin n) ℝ :=
  if hp : p.1 ∈ Ioc 0 h then update G φ κ (⟨p.1,hp.1,hp.2.trans hh1⟩,p.2)
  else G.covariance 0

theorem canonical_measurable (φ : Domain → EuclideanSpace ℝ (Fin n)) (hφ : Measurable φ)
    {h : ℝ} (hh1 : h ≤ 1) (κ : Domain → Matrix (Fin n) (Fin n) ℝ)
    (hκ : Measurable κ) (hκS : ∀ p, κ p ∈ constraint G) :
    Measurable (canonicalUpdate G φ hh1 κ) := by
  classical
  let s : Set Domain := {p | p.1 ∈ Ioc 0 h}
  have hp : Measurable (fun p : s =>
      ((⟨p.val.1,p.property.1,p.property.2.trans hh1⟩ : HeatCovarianceMeasure.Window),p.val.2)) :=
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_snd.comp measurable_subtype_coe)
  exact ((MatrixProfileUpdate.measurable G φ hφ κ hκ (upper G)
    (fun p => (hκS p).2)).comp hp).dite measurable_const
      (measurableSet_Ioc.preimage measurable_fst)

theorem canonical_mem (φ : Domain → EuclideanSpace ℝ (Fin n)) {h : ℝ} (hh1 : h ≤ 1)
    (κ : Domain → Matrix (Fin n) (Fin n) ℝ) (p : Domain) :
    canonicalUpdate G φ hh1 κ p ∈ constraint G := by
  classical
  unfold canonicalUpdate
  split_ifs with hp
  · exact ⟨MatrixProfileUpdate.elliptic G φ κ _,
      (MatrixProfileUpdate.norm_bound G φ κ _).trans (le_add_of_nonneg_right zero_le_one)⟩
  · exact baseline_mem G

theorem canonical_contraction (φ : Domain → EuclideanSpace ℝ (Fin n))
    {K β h D : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (κ η : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (hκS : ∀ p, κ p ∈ constraint G) (hηS : ∀ p, η p ∈ constraint G)
    (hD : 0 ≤ D) (hDiff : ∀ p, ‖κ p-η p‖ ≤ D) (p : Domain) :
    ‖canonicalUpdate G φ hh1 κ p-canonicalUpdate G φ hh1 η p‖ ≤
      (contractionConstant G K β*h^(β/4))*D := by
  classical
  unfold canonicalUpdate
  split_ifs with hp
  · have he := MatrixProfileUpdate.contraction G hK hβ hD hG φ κ η hκ hη
      (fun z => (hκS z).2) (fun z => (hηS z).2)
      (fun z => (hκS z).1.1) (fun z => (hηS z).1.1)
      (fun z => (hκS z).1.2) (fun z => (hηS z).1.2) hDiff
      (⟨p.1,hp.1,hp.2.trans hh1⟩,p.2)
    exact he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hp.1.le hp.2 (by positivity : 0 ≤ β/4))
      (contractionConstant_nonneg G hK)) hD)
  · rw [sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (contractionConstant_nonneg G hK) (Real.rpow_nonneg hh _)) hD

theorem exists_profile_horizon {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ contractionConstant G K β*h^(β/4) ≤ 1/2 := by
  obtain ⟨h,hh,hh1,hs⟩ := SHE.ProfileVolterra.exists_absorption_horizon (a := 0)
    (B := contractionConstant G K β/6) (θ := β/4) (by norm_num)
    (div_nonneg (contractionConstant_nonneg G hK) (by norm_num)) (by positivity)
  refine ⟨h,hh,hh1,?_⟩
  norm_num [SHE.ProfileVolterra.powerConstant] at hs
  exact hs

/-- A genuine coupled matrix Gaussian profile, constructed in the complete
space of bounded measurable elliptic matrix fields. -/
theorem exists_profile (φ : Domain → EuclideanSpace ℝ (Fin n)) (hφ : Measurable φ)
    {K β h : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hh : 0 < h) (hh1 : h ≤ 1)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (hsmall : contractionConstant G K β*h^(β/4) ≤ 1/2) :
    ∃ κ : Domain → Matrix (Fin n) (Fin n) ℝ, Measurable κ ∧ (∀ p, κ p ∈ constraint G) ∧
      ∀ r (hr : r ∈ Ioc 0 h) x,
        κ (r,x) = update G φ κ (⟨r,hr.1,hr.2.trans hh1⟩,x) := by
  let q := contractionConstant G K β*h^(β/4)
  have hq : 0 ≤ q := mul_nonneg (contractionConstant_nonneg G hK) (Real.rpow_nonneg hh.le _)
  obtain ⟨κ,hκ,hκS,hfix⟩ := BoundedMeasurableFixedPoint.exists_fixedPoint
    (constraint_closed G) (G.covariance 0) (baseline_mem G) (upper G) (fun _ hz => hz.2)
    (canonicalUpdate G φ hh1) (canonical_measurable G φ hφ hh1)
    (fun _ _ _ => canonical_mem G φ hh1 _) q hq (by dsimp [q]; linarith)
    (fun κ η hκ hη hκS hηS D hD hDiff p =>
      canonical_contraction G φ hK hβ.le hh.le hh1 hG κ η hκ hη hκS hηS hD hDiff p)
  refine ⟨κ,hκ,hκS,?_⟩
  intro r hr x
  have he := congrFun hfix (r,x)
  simpa only [canonicalUpdate, dif_pos hr] using he.symm

/-- Physical-time uniqueness is independent of the values chosen outside
the time horizon; the heat covariance only sees earlier positive times. -/
theorem profile_unique (φ : Domain → EuclideanSpace ℝ (Fin n))
    {K β h : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hh : 0 < h) (hh1 : h ≤ 1)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (hsmall : contractionConstant G K β*h^(β/4) ≤ 1/2)
    (κ η : Domain → Matrix (Fin n) (Fin n) ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (hκS : ∀ p, κ p ∈ constraint G) (hηS : ∀ p, η p ∈ constraint G)
    (hκfix : ∀ r (hr : r ∈ Ioc 0 h) x,
      κ (r,x) = update G φ κ (⟨r,hr.1,hr.2.trans hh1⟩,x))
    (hηfix : ∀ r (hr : r ∈ Ioc 0 h) x,
      η (r,x) = update G φ η (⟨r,hr.1,hr.2.trans hh1⟩,x)) :
    ∀ r ∈ Ioc 0 h, ∀ x, κ (r,x) = η (r,x) := by
  let f := extension G h κ
  let g := extension G h η
  let q := contractionConstant G K β*h^(β/4)
  have hq : 0 ≤ q := mul_nonneg (contractionConstant_nonneg G hK) (Real.rpow_nonneg hh.le _)
  have hf := extension_mem G (h := h) hκS
  have hg := extension_mem G (h := h) hηS
  have he : f = g := BoundedMeasurableFixedPoint.eq_of_contraction f g (upper G) q hq
    (by dsimp [q]; linarith) (fun p => (hf p).2) (fun p => (hg p).2) (by
      intro D hD hDiff p
      classical
      by_cases hp : p.1 ∈ Ioc 0 h
      · change ‖extension G h κ p-extension G h η p‖ ≤ _
        rw [extension,extension,if_pos hp,if_pos hp,hκfix p.1 hp p.2,hηfix p.1 hp p.2,
          ← update_extension G φ κ _ hp.2,← update_extension G φ η _ hp.2]
        have hb := MatrixProfileUpdate.contraction G hK hβ.le hD hG φ f g
          (extension_measurable G hκ) (extension_measurable G hη)
          (fun z => (hf z).2) (fun z => (hg z).2)
          (fun z => (hf z).1.1) (fun z => (hg z).1.1)
          (fun z => (hf z).1.2) (fun z => (hg z).1.2) hDiff
          (⟨p.1,hp.1,hp.2.trans hh1⟩,p.2)
        exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hp.1.le hp.2 (by positivity : 0 ≤ β/4))
          (contractionConstant_nonneg G hK)) hD)
      · change ‖extension G h κ p-extension G h η p‖ ≤ _
        rw [extension,extension,if_neg hp,if_neg hp,sub_self,norm_zero]
        exact mul_nonneg hq hD)
  intro r hr x
  have hb := congrFun he (r,x)
  simpa only [f,g,extension,if_pos hr] using hb

theorem exists_unique_profile_small_time (φ : Domain → EuclideanSpace ℝ (Fin n))
    (hφ : Measurable φ) {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β) :
    ∃ h : ℝ, ∃ hh1 : h ≤ 1, 0 < h ∧
      ∃ κ : Domain → Matrix (Fin n) (Fin n) ℝ, Measurable κ ∧ (∀ p, κ p ∈ constraint G) ∧
      (∀ r (hr : r ∈ Ioc 0 h) x, κ (r,x) = update G φ κ (⟨r,hr.1,hr.2.trans hh1⟩,x)) ∧
      ∀ η : Domain → Matrix (Fin n) (Fin n) ℝ, Measurable η → (∀ p, η p ∈ constraint G) →
        (∀ r (hr : r ∈ Ioc 0 h) x, η (r,x) = update G φ η (⟨r,hr.1,hr.2.trans hh1⟩,x)) →
        ∀ r ∈ Ioc 0 h, ∀ x, η (r,x) = κ (r,x) := by
  obtain ⟨h,hh,hh1,hs⟩ := exists_profile_horizon G hK hβ
  obtain ⟨κ,hκ,hκS,hfix⟩ := exists_profile G φ hφ hK hβ hh hh1 hG hs
  exact ⟨h,hh1,hh,κ,hκ,hκS,hfix,fun η hη hηS hηfix =>
    profile_unique G φ hK hβ hh hh1 hG hs η κ hη hκ hηS hκS hηfix hfix⟩

end SHEStochastic.MatrixProfileFixedPoint
