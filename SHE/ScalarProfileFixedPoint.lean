module

public import SHE.GaussianProfile
public import SHE.ProfileVolterra
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section
set_option autoImplicit false

/-! A complete bounded-measurable scalar profile realization for the actual Gaussian update. -/
noncomputable section
namespace SHE.ScalarProfileFixedPoint
open Set MeasureTheory Filter GaussianProfile StoppedFourier
open scoped ENNReal NNReal Topology

abbrev Domain := ℝ × HeatCircle
abbrev BoundedProfiles := lp (fun _ : Domain => ℝ) ∞

def profileSet (ell M : ℝ) : Set BoundedProfiles :=
  {f | Measurable (f : Domain → ℝ) ∧ ∀ p, f p ∈ Icc ell M}

theorem profileSet_closed (ell M : ℝ) : IsClosed (profileSet ell M) := by
  apply IsSeqClosed.isClosed
  intro u f hu hlim
  have hpoint : ∀ p, Tendsto (fun n => u n p) atTop (𝓝 (f p)) := by
    intro p
    exact ((lp.evalCLM ℝ (fun _ : Domain => ℝ) ∞ p).continuous.tendsto f).comp hlim
  refine ⟨measurable_of_tendsto_metrizable (fun n => (hu n).1) (tendsto_pi_nhds.mpr hpoint), ?_⟩
  intro p
  exact isClosed_Icc.mem_of_tendsto (hpoint p) (Eventually.of_forall (fun n => (hu n).2 p))

abbrev ProfileSpace (ell M : ℝ) := {f : BoundedProfiles // f ∈ profileSet ell M}

instance profileSpace_complete (ell M : ℝ) : CompleteSpace (ProfileSpace ell M) :=
  (profileSet_closed ell M).completeSpace_coe

theorem profileSpace_nonempty {ell M : ℝ} (horder : ell ≤ M) : Nonempty (ProfileSpace ell M) := by
  let f : BoundedProfiles := ⟨fun _ => ell, memℓp_infty ⟨‖ell‖, by rintro _ ⟨p, rfl⟩; exact le_rfl⟩⟩
  exact ⟨f, measurable_const, fun _ => ⟨le_rfl, horder⟩⟩

theorem update_exists {a : ℝ → ℝ} {φ : Domain → ℝ} {ell M h : ℝ}
    (ha : Measurable a) (hφ : Measurable φ) (hell : 0 ≤ ell) (hM : 0 ≤ M)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M) (f : ProfileSpace ell M) :
    ∃ g : ProfileSpace ell M, ∀ p : Domain,
      g.val p = if p.1 ∈ Ioc 0 h then positiveProfileUpdate a φ f.val p else ell := by
  classical
  let g : Domain → ℝ := fun p => if p.1 ∈ Ioc 0 h then positiveProfileUpdate a φ f.val p else ell
  have horder : ell ≤ M := (hal 0).trans (hau 0)
  have hg : ∀ p, g p ∈ Icc ell M := by
    intro p
    dsimp only [g]
    split_ifs
    · exact gaussianAverage_elliptic ha hell hM hal hau _ _
    · exact ⟨le_rfl, horder⟩
  have hgm : Measurable g := by
    exact (positiveProfileUpdate_measurable ha hφ f.property.1).ite
      (measurableSet_Ioc.preimage measurable_fst) measurable_const
  have hb : BddAbove (range fun p => ‖g p‖) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨p, rfl⟩
    change ‖g p‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_nonneg (hell.trans (hg p).1)]
    exact (hg p).2
  refine ⟨⟨⟨g, memℓp_infty hb⟩, hgm, hg⟩, ?_⟩
  intro p
  rfl

/-- Existence of a genuine bounded measurable scalar Gaussian profile. The
physical variance map, Hölder Gaussian derivative, joint measurability and
the complete function-space realization are all proved in the imported chain. -/
theorem exists_scalar_profile {a : ℝ → ℝ} {φ : Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hφ : Measurable φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2) :
    ∃ c : Domain → ℝ, Measurable c ∧ (∀ p, ell ≤ c p ∧ c p ≤ M) ∧
      ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x := by
  classical
  let q : ℝ := contractionConstant ell H β * h ^ (β / 4)
  have hq : 0 ≤ q := mul_nonneg (contractionConstant_nonneg hell.le hH) (Real.rpow_nonneg hh.le _)
  let K : ℝ≥0 := ⟨q, hq⟩
  let F : ProfileSpace ell M → ProfileSpace ell M := fun f =>
    Classical.choose (update_exists (h := h) ha hφ hell.le hM hal hau f)
  have happly : ∀ f p, (F f).val p =
      if p.1 ∈ Ioc 0 h then positiveProfileUpdate a φ f.val p else ell := by
    intro f p
    exact Classical.choose_spec (update_exists (h := h) ha hφ hell.le hM hal hau f) p
  have haB : ∀ z, |a z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hell.le.trans (hal z))]
    exact hau z
  have hLip : LipschitzWith K F := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖(F f).val - (F g).val‖ ≤ q * ‖f.val - g.val‖
    apply lp.norm_le_of_forall_le (mul_nonneg hq (norm_nonneg _))
    intro p
    change ‖(F f).val p - (F g).val p‖ ≤ _
    rw [happly, happly]
    by_cases hp : p.1 ∈ Ioc 0 h
    · rw [ite_eq_left hp, ite_eq_left hp, positiveProfileUpdate_eq hp.1.le p.2,
        positiveProfileUpdate_eq hp.1.le p.2, Real.norm_eq_abs]
      have hdiff : ∀ s ∈ Ioo 0 p.1, ∀ y, |f.val (s, y) - g.val (s, y)| ≤ ‖f.val - g.val‖ := by
        intro s hs y
        change ‖(f.val - g.val) (s, y)‖ ≤ _
        exact lp.norm_apply_le_norm (by norm_num : (∞ : ℝ≥0∞) ≠ 0) _ _
      have he := profileUpdate_contraction (φ := φ) ha f.property.1 g.property.1 hp.1 (hp.2.trans hh1)
        hell hM hH hβ.le (by linarith : β ≤ 2) (norm_nonneg _) haB hholder
        (fun s _ y => (f.property.2 (s, y)).1) (fun s _ y => (f.property.2 (s, y)).2)
        (fun s _ y => (g.property.2 (s, y)).1) (fun s _ y => (g.property.2 (s, y)).2) hdiff p.2
      exact he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hp.1.le hp.2 (by positivity : 0 ≤ β / 4))
          (contractionConstant_nonneg hell.le hH)) (norm_nonneg _))
    · rw [ite_eq_right hp, ite_eq_right hp, sub_self, norm_zero]
      positivity
  have hcon : ContractingWith K F := ⟨by change q < 1; dsimp [q]; linarith, hLip⟩
  let : Nonempty (ProfileSpace ell M) := profileSpace_nonempty ((hal 0).trans (hau 0))
  let c := hcon.fixedPoint F
  refine ⟨c.val, c.property.1, c.property.2, ?_⟩
  intro r hr x
  have he := congrArg (fun f : ProfileSpace ell M => f.val (r, x)) hcon.fixedPoint_isFixedPt
  change (F c).val (r, x) = c.val (r, x) at he
  rw [happly, ite_eq_left hr, positiveProfileUpdate_eq hr.1.le x] at he
  exact he.symm

theorem exists_profile_horizon {ell H β : ℝ} (hell : 0 ≤ ell) (hH : 0 ≤ H) (hβ : 0 < β) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2 := by
  obtain ⟨h, hh, hh1, hs⟩ := ProfileVolterra.exists_absorption_horizon (a := 0)
    (B := contractionConstant ell H β / 6) (θ := β / 4) (by norm_num)
    (div_nonneg (contractionConstant_nonneg hell hH) (by norm_num)) (by positivity)
  refine ⟨h, hh, hh1, ?_⟩
  norm_num [ProfileVolterra.powerConstant] at hs
  exact hs

/-- Uniqueness on the physical time horizon does not impose any condition on
the extension of a competing bounded measurable profile outside that horizon. -/
theorem scalar_profile_unique {a : ℝ → ℝ} {φ c d : Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hd : Measurable d) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M) (hdb : ∀ p, ell ≤ d p ∧ d p ≤ M)
    (hsmall : contractionConstant ell H β * h ^ (β / 4) ≤ 1 / 2)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x)
    (hdf : ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a φ d r x) :
    ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = d (r, x) := by
  let values : Set ℝ := (fun p : Domain => |c p - d p|) '' {p | p.1 ∈ Ioc 0 h}
  have hbounded : BddAbove values := by
    refine ⟨M, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have hcp := hcb p
    have hdp := hdb p
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hne : values.Nonempty := ⟨|c (h, 0) - d (h, 0)|, (h, 0), ⟨hh, le_rfl⟩, rfl⟩
  let D := sSup values
  have hDb : ∀ r ∈ Ioc 0 h, ∀ x, |c (r, x) - d (r, x)| ≤ D := by
    intro r hr x
    exact le_csSup hbounded ⟨(r, x), hr, rfl⟩
  have hD : 0 ≤ D := (abs_nonneg (c (h, 0) - d (h, 0))).trans (hDb h ⟨hh, le_rfl⟩ 0)
  have haB : ∀ z, |a z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hell.le.trans (hal z))]
    exact hau z
  have hstep : ∀ r ∈ Ioc 0 h, ∀ x, |c (r, x) - d (r, x)| ≤
      (contractionConstant ell H β * h ^ (β / 4)) * D := by
    intro r hr x
    rw [hcf r hr x, hdf r hr x]
    have he := profileUpdate_contraction (φ := φ) ha hc hd hr.1 (hr.2.trans hh1)
      hell hM hH hβ.le (by linarith : β ≤ 2) hD haB hholder
      (fun s _ y => (hcb (s, y)).1) (fun s _ y => (hcb (s, y)).2)
      (fun s _ y => (hdb (s, y)).1) (fun s _ y => (hdb (s, y)).2)
      (fun s hs y => hDb s ⟨hs.1, hs.2.le.trans hr.2⟩ y) x
    exact he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.1.le hr.2 (by positivity : 0 ≤ β / 4))
      (contractionConstant_nonneg hell.le hH)) hD)
  have hsup : D ≤ (contractionConstant ell H β * h ^ (β / 4)) * D := by
    apply csSup_le hne
    rintro _ ⟨p, hp, rfl⟩
    exact hstep p.1 hp p.2
  have hzero : D = 0 := by
    have he := mul_le_mul_of_nonneg_right hsmall hD
    linarith
  intro r hr x
  have he := hDb r hr x
  rw [hzero] at he
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

theorem exists_unique_scalar_profile_small_time {a : ℝ → ℝ} {φ : Domain → ℝ} {ell M H β : ℝ}
    (ha : Measurable a) (hφ : Measurable φ) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∃ c : Domain → ℝ,
      Measurable c ∧ (∀ p, ell ≤ c p ∧ c p ≤ M) ∧
      (∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x) ∧
      ∀ d : Domain → ℝ, Measurable d → (∀ p, ell ≤ d p ∧ d p ≤ M) →
        (∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = profileUpdate a φ d r x) →
        ∀ r ∈ Ioc 0 h, ∀ x, d (r, x) = c (r, x) := by
  obtain ⟨h, hh, hh1, hsmall⟩ := exists_profile_horizon hell.le hH hβ
  obtain ⟨c, hc, hcb, hcf⟩ := exists_scalar_profile ha hφ hell hM hH hβ hβ1 hh hh1 hal hau hholder hsmall
  refine ⟨h, hh, hh1, c, hc, hcb, hcf, ?_⟩
  intro d hd hdb hdf
  exact scalar_profile_unique ha hd hc hell hM hH hβ hβ1 hh hh1 hal hau hholder hdb hcb hsmall hdf hcf

/-- The constructed scalar profiles, and every exact bounded measurable scalar
profile, satisfy the actual Gaussian displacement display. -/
theorem scalar_profile_displacement {a : ℝ → ℝ} {φ c : Domain → ℝ} {ell M H β h : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hell : 0 < ell) (hM : 0 ≤ M)
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (hh1 : h ≤ 1)
    (hal : ∀ z, ell ≤ a z) (hau : ∀ z, a z ≤ M)
    (hholder : ∀ z w, |a z - a w| ≤ H * |z - w| ^ β)
    (hcb : ∀ p, ell ≤ c p ∧ c p ≤ M)
    (hcf : ∀ r ∈ Ioc 0 h, ∀ x, c (r, x) = profileUpdate a φ c r x)
    (r : ℝ) (hr : r ∈ Ioc 0 h) (x : HeatCircle) :
    |c (r, x) - a (φ (r, x))| ≤
      H * GaussianAudit.gaussianAbsMoment β * (ProfileVariance.upperConstant * M) ^ (β / 2) * r ^ (β / 4) := by
  rw [hcf r hr x]
  have haB : ∀ z, |a z| ≤ M := by
    intro z
    rw [abs_of_nonneg (hell.le.trans (hal z))]
    exact hau z
  exact profileUpdate_displacement ha hc hr.1 (hr.2.trans hh1) hell hM hH hβ haB hholder
    (fun s _ y => (hcb (s, y)).1) (fun s _ y => (hcb (s, y)).2) x

end SHE.ScalarProfileFixedPoint
