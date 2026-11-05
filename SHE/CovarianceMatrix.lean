module

public import SHE.WordRecursion
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CovarianceMatrix
open MeasureTheory Set Finset Matrix SHE.WordRecursion SHE.ProfileVariance SHE.StoppedFourier
open scoped ENNReal
local instance covarianceCirclePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem integral_quadratic {α : Type*} [MeasurableSpace α] (μ : Measure α) {n : ℕ}
    (A : α → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j,Integrable (fun x => A x i j) μ)
    (z : Fin n → ℝ) :
    (∫ x,star z ⬝ᵥ (A x *ᵥ z) ∂μ) = star z ⬝ᵥ ((fun i j => ∫ x,A x i j ∂μ) *ᵥ z) := by
  classical
  simp only [dotProduct,mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
  have hterm (i j : Fin n) : Integrable (fun x => z i*(A x i j*z j)) μ :=
    ((hA i j).mul_const (z j)).const_mul (z i)
  rw [integral_finsetSum univ (fun i _ => integrable_finsetSum univ (fun j _ => hterm i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum univ (fun j _ => hterm i j)]
  simp only [integral_mul_const,integral_const_mul]

/-- Integrating actual finite positive semidefinite matrices preserves
positivity, with entrywise integrability checked explicitly. -/
theorem entry_integral_posSemidef {α : Type*} [MeasurableSpace α] (μ : Measure α) {n : ℕ}
    (A : α → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j,Integrable (fun x => A x i j) μ)
    (hpos : ∀ᵐ x ∂μ,(A x).PosSemidef) :
    Matrix.PosSemidef (fun i j => ∫ x,A x i j ∂μ) := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    simpa only [star_trivial] using hx.isHermitian.apply i j
  · intro z
    rw [← integral_quadratic μ A hA z]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact hx.dotProduct_mulVec_nonneg z

def heatRowBound (δ : ℝ) : ℝ := 1+heatConstant*(δ/2)^(-(1/2:ℝ))

theorem heatRowBound_pos {δ : ℝ} (hδ : 0 < δ) : 0 < heatRowBound δ := by
  unfold heatRowBound
  have hC := heatConstant_pos
  positivity

theorem heatRow_measurable {n : ℕ} (Z : Fin n → Observation) (i : Fin n) :
    Measurable (fun p : ℝ × HeatCircle => heatRow Z p.1 p.2 i) := by
  exact Complex.measurable_re.comp ((heatPhysical_measurable (Z i).center).comp
    ((measurable_const.sub measurable_fst).prodMk measurable_snd))

theorem covarianceDensity_measurable {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) (i j : Fin n) :
    Measurable (fun t => covarianceDensity c Z t i j) :=
  (((hc.mul (heatRow_measurable Z i)).mul (heatRow_measurable Z j)).stronglyMeasurable.integral_prod_right).measurable

theorem heatRow_bound {n : ℕ} (Z : Fin n → Observation) {δ s t : ℝ}
    (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-s) (ht : t ≤ s)
    (x : HeatCircle) (i : Fin n) : |heatRow Z t x i| ≤ heatRowBound δ := by
  exact heatPhysical_re_bound hδ (by linarith [hgap i]) _ _

theorem density_integrand_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) {δ M s t : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (ht : t ≤ s)
    (hc : ∀ x,|c (t,x)| ≤ M) (i j : Fin n) (x : HeatCircle) :
    |c (t,x)*heatRow Z t x i*heatRow Z t x j| ≤ M*(heatRowBound δ)^2 := by
  rw [abs_mul,abs_mul]
  have hB := (heatRowBound_pos hδ).le
  have hh := mul_le_mul (mul_le_mul (hc x) (heatRow_bound Z hδ hgap ht x i)
    (abs_nonneg _) hM) (heatRow_bound Z hδ hgap ht x j) (abs_nonneg _) (mul_nonneg hM hB)
  nlinarith only [hh]

theorem covariance_spatial_integrable {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M s t : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hgap : ∀ i,δ ≤ (Z i).target-s) (ht : t ≤ s)
    (hbound : ∀ x,|c (t,x)| ≤ M) (i j : Fin n) :
    Integrable (fun x : HeatCircle => c (t,x)*heatRow Z t x i*heatRow Z t x j) AddCircle.haarAddCircle := by
  have hm : Measurable (fun x : HeatCircle => c (t,x)*heatRow Z t x i*heatRow Z t x j) := ((hc.mul (heatRow_measurable Z i)).mul (heatRow_measurable Z j)).comp
    (measurable_const.prodMk measurable_id)
  apply (integrable_const (M*(heatRowBound δ)^2)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using density_integrand_bound c Z hδ hM hgap ht hbound i j x)

theorem covarianceDensity_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M s t : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hgap : ∀ i,δ ≤ (Z i).target-s) (ht : t ≤ s)
    (hbound : ∀ x,|c (t,x)| ≤ M) (i j : Fin n) :
    |covarianceDensity c Z t i j| ≤ M*(heatRowBound δ)^2 := by
  have hi := covariance_spatial_integrable c hc Z hδ hM hgap ht hbound i j
  change ‖∫ x : HeatCircle,c (t,x)*heatRow Z t x i*heatRow Z t x j ∂AddCircle.haarAddCircle‖ ≤ _
  calc
    _ ≤ ∫ x : HeatCircle,‖c (t,x)*heatRow Z t x i*heatRow Z t x j‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _x : HeatCircle,M*(heatRowBound δ)^2 ∂AddCircle.haarAddCircle := by
      apply integral_mono hi.norm (integrable_const _)
      intro x
      exact density_integrand_bound c Z hδ hM hgap ht hbound i j x
    _ = _ := by simp

theorem covariance_entry_intervalIntegrable {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M q s : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hqs : q ≤ s) (hgap : ∀ i,δ ≤ (Z i).target-s)
    (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) (i j : Fin n) :
    IntervalIntegrable (fun t => covarianceDensity c Z t i j) volume q s := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hqs).mpr
  apply (integrable_const (M*(heatRowBound δ)^2)).mono'
    (covarianceDensity_measurable c hc Z i j).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa only [Real.norm_eq_abs] using covarianceDensity_bound c hc Z hδ hM hgap ht.2 (hbound t ht) i j

theorem covarianceDensity_posSemidef {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (hc : Measurable c) (Z : Fin n → Observation) {δ M s t : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hgap : ∀ i,δ ≤ (Z i).target-s) (ht : t ≤ s)
    (hbound : ∀ x,|c (t,x)| ≤ M) (hnonneg : ∀ x,0 ≤ c (t,x)) :
    Matrix.PosSemidef (fun i j => covarianceDensity c Z t i j) := by
  let A (x : HeatCircle) : Matrix (Fin n) (Fin n) ℝ :=
    c (t,x) • Matrix.vecMulVec (fun i => heatRow Z t x i) (fun i => heatRow Z t x i)
  have hA (i j : Fin n) : Integrable (fun x => A x i j) AddCircle.haarAddCircle := by
    simpa only [A,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec,Matrix.of_apply,mul_assoc] using
      covariance_spatial_integrable c hc Z hδ hM hgap ht hbound i j
  have hpos : ∀ x,(A x).PosSemidef := by
    intro x
    simpa only [A,Pi.star_apply,star_trivial] using
      (Matrix.posSemidef_vecMulVec_self_star (fun i => heatRow Z t x i)).smul (hnonneg x)
  have hh := entry_integral_posSemidef AddCircle.haarAddCircle A hA (ae_of_all _ hpos)
  simpa only [A,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec,Matrix.of_apply,mul_assoc,covarianceDensity] using hh

/-- Actual backward observation covariance is positive semidefinite,
including colliding observations and singular covariance ranges. The
window stays explicitly before every target by a positive heat gap. -/
theorem covariance_posSemidef {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hqs : q ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Icc q s,∀ x,0 ≤ c (t,x)) : (covariance c Z q s).PosSemidef := by
  unfold covariance
  simp only [intervalIntegral.integral_of_le hqs]
  apply entry_integral_posSemidef (volume.restrict (Ioc q s))
    (fun t i j => covarianceDensity c Z t i j)
    (fun i j => (covariance_entry_intervalIntegrable c hc Z hδ hM hqs hgap hbound i j).1)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact covarianceDensity_posSemidef c hc Z hδ hM hgap ht.2
    (hbound t (Ioc_subset_Icc_self ht)) (hnonneg t (Ioc_subset_Icc_self ht))

theorem covariance_entry_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hqs : q ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M)
    (i j : Fin n) : |covariance c Z q s i j| ≤ M*(heatRowBound δ)^2*(s-q) := by
  have hb (t : ℝ) (ht : t ∈ uIoc q s) : ‖covarianceDensity c Z t i j‖ ≤ M*(heatRowBound δ)^2 := by
    rw [uIoc_of_le hqs] at ht
    exact covarianceDensity_bound c hc Z hδ hM hgap ht.2 (hbound t (Ioc_subset_Icc_self ht)) i j
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hqs),covariance] using hh

theorem covariance_trace_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hqs : q ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) :
    (covariance c Z q s).trace ≤ (n:ℝ)*M*(heatRowBound δ)^2*(s-q) := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ _i : Fin n,M*(heatRowBound δ)^2*(s-q) := sum_le_sum (fun i _ =>
      (le_abs_self _).trans (covariance_entry_bound c hc Z hδ hM hqs hgap hbound i i))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];ring

theorem covariance_add_interval {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q r s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hqr : q ≤ r) (hrs : r ≤ s) (hgap : ∀ i,δ ≤ (Z i).target-s)
    (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) :
    covariance c Z q s = covariance c Z q r+covariance c Z r s := by
  apply Matrix.ext
  intro i j
  have hi := covariance_entry_intervalIntegrable c hc Z hδ hM (hqr.trans hrs) hgap hbound i j
  have h₁ : IntervalIntegrable (fun t => covarianceDensity c Z t i j) volume q r :=
    hi.mono_set (by simpa only [uIcc_of_le hqr,uIcc_of_le (hqr.trans hrs)] using Icc_subset_Icc le_rfl hrs)
  have h₂ : IntervalIntegrable (fun t => covarianceDensity c Z t i j) volume r s :=
    hi.mono_set (by simpa only [uIcc_of_le hrs,uIcc_of_le (hqr.trans hrs)] using Icc_subset_Icc hqr le_rfl)
  exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm

@[simp] theorem covariance_self {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (s : ℝ) : covariance c Z s s = 0 := by
  ext i j
  simp [covariance]

@[simp] theorem multivariateGaussian_zero_covariance {n : ℕ} (m : State n) :
    ProbabilityTheory.multivariateGaussian m 0 = Measure.dirac m := by
  simp [ProbabilityTheory.multivariateGaussian]

@[simp] theorem gaussianSemigroup_terminal {n : ℕ} (c : ℝ × HeatCircle → ℝ)
    (Z : Fin n → Observation) (s : ℝ) (F : State n → ℝ) (z : State n) :
    gaussianSemigroup c Z s s F z = F z := by
  simp [gaussianSemigroup]

theorem covariance_entry_hasDerivAt_left {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hqs : q ≤ s)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M)
    (i j : Fin n) (hcont : ContinuousAt (fun t => covarianceDensity c Z t i j) q) :
    HasDerivAt (fun r => covariance c Z r s i j) (-covarianceDensity c Z q i j) q :=
  intervalIntegral.integral_hasDerivAt_left
    (covariance_entry_intervalIntegrable c hc Z hδ hM hqs hgap hbound i j)
    (covarianceDensity_measurable c hc Z i j).aestronglyMeasurable.stronglyMeasurableAtFilter hcont

/-- The actual backward covariance has its expected derivative almost
everywhere even for a merely measurable bounded reference coefficient. -/
theorem covariance_entry_ae_hasDerivAt_left {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M a b s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hab : a ≤ b)
    (hgap : ∀ i,δ ≤ (Z i).target-b) (hbound : ∀ t ∈ Icc a b,∀ x,|c (t,x)| ≤ M)
    (hs : s ∈ Icc a b) (i j : Fin n) :
    ∀ᵐ q : ℝ,q ∈ Icc a b →
      HasDerivAt (fun r => covariance c Z r s i j) (-covarianceDensity c Z q i j) q := by
  have hi := covariance_entry_intervalIntegrable c hc Z hδ hM hab hgap hbound i j
  filter_upwards [hi.ae_hasDerivAt_integral] with q hq
  intro hqa
  have hh := (hq (by simpa only [uIcc_of_le hab] using hqa) s
    (by simpa only [uIcc_of_le hab] using hs)).neg
  have he : (fun r => -(∫ t in s..r,covarianceDensity c Z t i j)) =
      fun r => covariance c Z r s i j := by
    funext r
    rw [intervalIntegral.integral_symm,neg_neg]
    rfl
  change HasDerivAt (fun r => -(∫ t in s..r,covarianceDensity c Z t i j)) (-covarianceDensity c Z q i j) q at hh
  rwa [he] at hh

theorem covariance_increment_posSemidef {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q r s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hqr : q ≤ r) (hrs : r ≤ s) (hgap : ∀ i,δ ≤ (Z i).target-s)
    (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M)
    (hnonneg : ∀ t ∈ Icc q s,∀ x,0 ≤ c (t,x)) :
    (covariance c Z q s-covariance c Z r s).PosSemidef := by
  rw [covariance_add_interval c hc Z hδ hM hqr hrs hgap hbound,add_sub_cancel_right]
  exact covariance_posSemidef c hc Z hδ hM hqr (fun i => by linarith [hgap i])
    (fun t ht => hbound t ⟨ht.1,ht.2.trans hrs⟩)
    (fun t ht => hnonneg t ⟨ht.1,ht.2.trans hrs⟩)

theorem covariance_increment_trace_bound {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M q r s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hqr : q ≤ r) (hrs : r ≤ s) (hgap : ∀ i,δ ≤ (Z i).target-s)
    (hbound : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) :
    (covariance c Z q s-covariance c Z r s).trace ≤
      (n:ℝ)*M*(heatRowBound δ)^2*(r-q) := by
  rw [covariance_add_interval c hc Z hδ hM hqr hrs hgap hbound,add_sub_cancel_right]
  exact covariance_trace_bound c hc Z hδ hM hqr (fun i => by linarith [hgap i])
    (fun t ht => hbound t ⟨ht.1,ht.2.trans hrs⟩)

def densityMatrix {n : ℕ} (c : ℝ × HeatCircle → ℝ) (Z : Fin n → Observation) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => covarianceDensity c Z t i j

theorem covariance_ae_hasDerivAt_left {n : ℕ} (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : Fin n → Observation) {δ M a b s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hab : a ≤ b)
    (hgap : ∀ i,δ ≤ (Z i).target-b) (hbound : ∀ t ∈ Icc a b,∀ x,|c (t,x)| ≤ M)
    (hs : s ∈ Icc a b) :
    ∀ᵐ q : ℝ,q ∈ Icc a b → HasDerivAt (fun r => covariance c Z r s) (-densityMatrix c Z q) q := by
  have hh := ae_all_iff.mpr (fun i : Fin n => ae_all_iff.mpr (fun j : Fin n =>
    covariance_entry_ae_hasDerivAt_left c hc Z hδ hM hab hgap hbound hs i j))
  filter_upwards [hh] with q hq
  intro hqa
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hq i j hqa

end SHE.CovarianceMatrix
