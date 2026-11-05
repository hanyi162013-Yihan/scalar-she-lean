module

public import SHE.ProfileReserveCalculus
public import SHE.ClippedCovariance
public import SHE.LipschitzOpenIntegral
public import SHE.FiniteWordScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.EllipticGaussianSegment
open Set Filter MeasureTheory ProbabilityTheory GaussianIncrement GaussianProfileMark
  GaussianRangeSmooth GaussianConvolution MeasurableGaussianScores
open scoped Topology NNReal
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def segment (c₀ c₁ : X → ℝ) (t : ℝ) (x : X) : ℝ := (1-t)*c₀ x+t*c₁ x
def clipped (c₀ c₁ : X → ℝ) (t : ℝ) : X → ℝ := segment c₀ c₁ (ClippedCovariance.clip 0 1 t)

theorem clipped_bounds (c₀ c₁ : X → ℝ) {ell M : ℝ}
    (h₀ : ∀ x,ell≤c₀ x ∧ c₀ x≤M) (h₁ : ∀ x,ell≤c₁ x ∧ c₁ x≤M) (t : ℝ) (x : X) :
    ell≤clipped c₀ c₁ t x ∧ clipped c₀ c₁ t x≤M := by
  have ht:=ClippedCovariance.clip_mem (by norm_num : (0:ℝ)≤1) t
  dsimp [clipped,segment]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (h₀ x).1),
      mul_nonneg ht.1 (sub_nonneg.mpr (h₁ x).1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (h₀ x).2),
      mul_nonneg ht.1 (sub_nonneg.mpr (h₁ x).2)]

theorem clipped_lipschitz (c₀ c₁ : X → ℝ) (x : X) :
    LipschitzWith (Real.nnabs |c₁ x-c₀ x|) (fun t=>clipped c₀ c₁ t x) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hh:=(ClippedCovariance.lipschitz_clip 0 1).dist_le_mul s t
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hh
  rw [Real.dist_eq,Real.dist_eq,Real.coe_nnabs,abs_abs]
  calc
    _=|c₁ x-c₀ x| * |ClippedCovariance.clip 0 1 s-ClippedCovariance.clip 0 1 t| := by
      rw [←abs_mul]
      congr 1
      dsimp [clipped,segment]
      ring
    _≤_:=mul_le_mul_of_nonneg_left hh (abs_nonneg _)

theorem clipped_hasDerivAt (c₀ c₁ : X → ℝ) (x : X) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (fun s=>clipped c₀ c₁ s x) (c₁ x-c₀ x) t := by
  have hc : HasDerivAt (ClippedCovariance.clip 0 1) 1 t :=
    (hasDerivAt_id t).congr_of_eventuallyEq (ClippedCovariance.clip_eq_near ht)
  have hh := (hc.mul_const (c₁ x-c₀ x)).const_add (c₀ x)
  convert! hh using 1
  · funext s
    dsimp [clipped,segment]
    ring
  · ring

/-- Exact finite covariance comparison for arbitrary bounded Borel tests,
including singular covariance and arbitrary base means. The whole segment
uses the actual convex coefficient law. Integrability at BOTH endpoints is
derived from a genuine Gaussian reserve, rather than a positive-age limit. -/
theorem covariance_ftc (μ : Measure X) (c₀ c₁ : X → ℝ)
    (hc₀ : Measurable c₀) (hc₁ : Measurable c₁) {ell M : ℝ} (hell : 0<ell)
    (h₀ : ∀ x,ell≤c₀ x ∧ c₀ x≤M) (h₁ : ∀ x,ell≤c₁ x ∧ c₁ x≤M)
    (row : X → State n) (hrow : Measurable row)
    (henergy : Integrable (fun x=>‖row x‖^2) μ)
    (F : State n→ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ y,|F y|≤B) (mean : State n) :
    let mark := fun t=>FiniteWordScores.covarianceMark μ
      (profileCovariance μ (segment c₀ c₁ t) row) (fun x=>c₁ x-c₀ x) row F mean
    IntervalIntegrable mark volume 0 1 ∧
      (∫ t in (0:ℝ)..1,mark t)=gaussianAverage (profileCovariance μ c₁ row) F mean-
        gaussianAverage (profileCovariance μ c₀ row) F mean := by
  intro mark
  let c:=clipped c₀ c₁
  let g:=fun x=>|c₁ x-c₀ x|
  have hcm (t) : Measurable (c t) :=
    (hc₀.const_mul (1-ClippedCovariance.clip 0 1 t)).add
      (hc₁.const_mul (ClippedCovariance.clip 0 1 t))
  have hcb (t x) : |c t x|≤M := by
    rw [abs_of_nonneg (hell.le.trans (clipped_bounds c₀ c₁ h₀ h₁ t x).1)]
    exact (clipped_bounds c₀ c₁ h₀ h₁ t x).2
  have hci (t) : Integrable (fun x=>|c t x| *‖row x‖^2) μ := by
    apply (henergy.const_mul M).mono'
      ((((continuous_abs.measurable.comp (hcm t))).mul (hrow.norm.pow_const 2)).aestronglyMeasurable)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hcb t x) (sq_nonneg _)
  have hgb (x) : g x≤2*M := by
    have h0 : |c₀ x|≤M := by rw [abs_of_nonneg (hell.le.trans (h₀ x).1)]; exact (h₀ x).2
    have h1 : |c₁ x|≤M := by rw [abs_of_nonneg (hell.le.trans (h₁ x).1)]; exact (h₁ x).2
    exact (abs_sub (c₁ x) (c₀ x)).trans ((add_le_add h1 h0).trans_eq (by ring))
  have hgm : Measurable g := continuous_abs.measurable.comp (hc₁.sub hc₀)
  have hgi : Integrable (fun x=>g x*‖row x‖^2) μ := by
    apply (henergy.const_mul (2*M)).mono'
      ((hgm.mul (hrow.norm.pow_const 2)).aestronglyMeasurable)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hgb x) (sq_nonneg _)
  have hlip : ∀ᵐ x ∂μ,LipschitzWith (Real.nnabs (g x)) (fun t=>c t x) :=
    ae_of_all _ (clipped_lipschitz c₀ c₁)
  obtain ⟨Q,K,hK⟩ := exists_uniform_profile_reserve μ hell c row hrow.aestronglyMeasurable henergy
    (fun t=>(hcm t).aestronglyMeasurable) hci
    (fun t=>ae_of_all _ (fun x=>(clipped_bounds c₀ c₁ h₀ h₁ t x).1)) g
    (ae_of_all _ (fun x=>abs_nonneg _)) hgi hlip
  obtain ⟨L,hL⟩ := Q.exists_lipschitz_fixed_mean hK F hF B hB mean
  have hd (t : ℝ) (ht : t∈Ioo 0 1) :
      HasDerivAt (fun s=>gaussianAverage (profileCovariance μ (c s) row) F mean) (mark t) t := by
    have hh:=hasDerivAt_profile_borel_of_uniform_floor μ hell c (fun x=>c₁ x-c₀ x) row
      hrow.aestronglyMeasurable henergy (fun t=>(hcm t).aestronglyMeasurable) hci
      (fun t=>ae_of_all _ (fun x=>(clipped_bounds c₀ c₁ h₀ h₁ t x).1))
      (hc₁.sub hc₀).aestronglyMeasurable g (ae_of_all _ (fun x=>abs_nonneg _)) hgi hlip
      (ae_of_all _ (fun x=>clipped_hasDerivAt c₀ c₁ x ht)) F hF B hB mean
    have he : c t=segment c₀ c₁ t := by
      dsimp [c,clipped]
      rw [ClippedCovariance.clip_eq (Ioo_subset_Icc_self ht)]
    simpa only [he,mark,FiniteWordScores.covarianceMark] using hh
  have hh:=LipschitzIntegralIdentity.integral_eq_sub_on_open hL (by norm_num : (0:ℝ)≤1) hd
  have h0 : c 0=c₀ := by funext x; simp [c,clipped,segment,ClippedCovariance.clip]
  have h1 : c 1=c₁ := by funext x; simp [c,clipped,segment,ClippedCovariance.clip]
  simpa only [h0,h1] using hh

end SHE.EllipticGaussianSegment
