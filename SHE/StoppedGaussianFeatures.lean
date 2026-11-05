module

public import SHE.RealHeatScore
public import SHE.GaussianAudit
public import SHE.WordRecursion
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual weighted real Gaussian features for individually stopped physical
heat histories. Every stopping indicator remains inside its own physical
feature; no common-window covariance is substituted for this Gram. -/
noncomputable section
namespace SHE.StoppedGaussianFeatures
open Set MeasureTheory AddCircle Finset StoppedFourier ProfileVariance WordRecursion
  GaussianGramScore GaussianAudit
open scoped InnerProductSpace Matrix.Norms.L2Operator Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Domain := ℝ × HeatCircle

def historyMeasure (q : ℝ) : Measure Domain :=
  (volume.restrict (Ici q)).prod (haarAddCircle (T := 2 * Real.pi))

instance historyMeasure_sfinite (q : ℝ) : SFinite (historyMeasure q) := by
  unfold historyMeasure
  infer_instance

theorem physicalCircleHeat_eq (t : ℝ) (x y : HeatCircle) :
    physicalCircleHeat t x y = heatPhysical t x y := by
  apply tsum_congr
  intro k
  simp only [heatCoeff]
  ring

variable {n : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)

def stoppedRow (p : Domain) : State n :=
  WithLp.toLp 2 (fun i => if p.1 < σ i then
    (heatPhysical (target i - p.1) (center i) p.2).re else 0)

def realHistory (z : State n) (p : Domain) : ℝ :=
  ∑ i, z i * stoppedRow σ target center p i

theorem stoppedRow_entry_measurable (i : Fin n) :
    Measurable (fun p : Domain => stoppedRow σ target center p i) := by
  apply Measurable.ite (measurableSet_lt measurable_fst measurable_const)
  · exact Complex.measurable_re.comp ((heatPhysical_measurable (center i)).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))
  · exact measurable_const

theorem stoppedRow_measurable : Measurable (stoppedRow σ target center) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact Measurable.of_eval (stoppedRow_entry_measurable σ target center)

theorem realHistory_measurable (z : State n) : Measurable (realHistory σ target center z) := by
  exact Finset.measurable_fun_sum univ (fun i _ =>
    (stoppedRow_entry_measurable σ target center i).const_mul (z i))

/-- The real stopped row is exactly the real physical history in the Fourier
construction, with all original stopping indicators retained. -/
theorem physicalHistory_eq_realHistory (hages : ∀ i, σ i ≤ target i) (z : State n) (p : Domain) :
    physicalHistory (fun i => (z i : ℂ)) σ target center p =
      (realHistory σ target center z p : ℂ) := by
  unfold physicalHistory realHistory
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro i _
  by_cases hp : p.1 < σ i
  · have ht : 0 < target i - p.1 := by linarith [hages i]
    simp only [stoppedRow, ite_eq_left hp]
    rw [physicalCircleHeat_eq, ← heatPhysical_real ht]
    push_cast
    rfl
  · simp only [stoppedRow, ite_eq_right hp, mul_zero,
      Complex.ofReal_zero]

theorem realHistory_square_ae (hages : ∀ i, σ i ≤ target i) (z : State n) (u : ℝ) :
    (fun y => realHistory σ target center z (u, y) ^ 2) =ᵐ[haarAddCircle]
      (fun y => ‖historyF univ (fun i => (z i : ℂ)) σ target center u y‖ ^ 2) := by
  filter_upwards [physicalHistory_ae (fun i => (z i : ℂ)) σ target center hages u] with y hy
  rw [physicalHistory_eq_realHistory σ target center hages] at hy
  rw [← hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem realHistory_square_integrable (hages : ∀ i, σ i ≤ target i) (z : State n) (u : ℝ) :
    Integrable (fun y => realHistory σ target center z (u, y) ^ 2) haarAddCircle := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.memLp (historyF univ (fun i => (z i : ℂ)) σ target center u)).aestronglyMeasurable).mp
      (Lp.memLp (historyF univ (fun i => (z i : ℂ)) σ target center u))
  exact hi.congr (realHistory_square_ae σ target center hages z u).symm

theorem realHistory_square_mass (hages : ∀ i, σ i ≤ target i) (z : State n) (u : ℝ) :
    (∫ y, realHistory σ target center z (u, y) ^ 2 ∂haarAddCircle) =
      ‖historyF univ (fun i => (z i : ℂ)) σ target center u‖ ^ 2 := by
  rw [L2_norm_sq_eq_integral]
  exact integral_congr_ae (realHistory_square_ae σ target center hages z u)

/-- Genuine time-space square integrability of the individually stopped
physical row, obtained from the original full stopped-history energy. -/
theorem realHistory_square_product_integrable (hages : ∀ i, σ i ≤ target i)
    (z : State n) (q : ℝ) :
    Integrable (fun p => realHistory σ target center z p ^ 2) (historyMeasure q) := by
  have hm := ((realHistory_measurable σ target center z).pow_const (2 : ℕ)).aestronglyMeasurable
    (μ := historyMeasure q)
  apply (integrable_prod_iff hm).mpr
  refine ⟨ae_of_all _ (realHistory_square_integrable σ target center hages z), ?_⟩
  have ht := historyF_memLp_time univ (fun i => (z i : ℂ)) σ target center
    (fun i _ => hages i) q
  have hi := (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mp ht
  have heq : (fun u => ∫ y, ‖realHistory σ target center z (u, y) ^ 2‖ ∂haarAddCircle) =
      fun u => ‖historyF univ (fun i => (z i : ℂ)) σ target center u‖ ^ 2 := by
    funext u
    have habs (y : HeatCircle) : ‖realHistory σ target center z (u, y) ^ 2‖ =
        realHistory σ target center z (u, y) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    simp_rw [habs]
    exact realHistory_square_mass σ target center hages z u
  rw [heq]
  exact hi

/-- The physical product-space energy equals the original full-history
energy, rather than merely being bounded by it. -/
theorem realHistory_full_energy (hages : ∀ i, σ i ≤ target i) (z : State n) (q : ℝ) :
    (∫ p, realHistory σ target center z p ^ 2 ∂historyMeasure q) =
      (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target center) q).toReal := by
  have hi := realHistory_square_product_integrable σ target center hages z q
  rw [historyMeasure, integral_prod _ hi]
  simp_rw [realHistory_square_mass σ target center hages z]
  have ht := historyF_memLp_time univ (fun i => (z i : ℂ)) σ target center
    (fun i _ => hages i) q
  rw [memLp_fullEnergy_norm_sq ht, toLp_norm_sq_eq_integral]

def basisCoeff (i : Fin n) : State n := WithLp.toLp 2 (Pi.single i 1)

theorem realHistory_basisCoeff (i : Fin n) (p : Domain) :
    realHistory σ target center (basisCoeff i) p = stoppedRow σ target center p i := by
  change (∑ j : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) j *
    stoppedRow σ target center p j) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']

def weightedFunction (c : Domain → ℝ) (i : Fin n) (p : Domain) : ℝ :=
  Real.sqrt (c p) * stoppedRow σ target center p i

theorem weightedFunction_measurable {c : Domain → ℝ} (hc : Measurable c) (i : Fin n) :
    Measurable (weightedFunction σ target center c i) :=
  (Real.continuous_sqrt.measurable.comp hc).mul (stoppedRow_entry_measurable σ target center i)

theorem weightedFunction_square {c : Domain → ℝ} (hc0 : ∀ p, 0 ≤ c p)
    (i : Fin n) (p : Domain) : weightedFunction σ target center c i p ^ 2 =
      c p * stoppedRow σ target center p i ^ 2 := by
  rw [weightedFunction, mul_pow, Real.sq_sqrt (hc0 p)]

/-- The actual square-root weighted stopped physical features belong to the
real time-space L² space. This is a conclusion from bounded elliptic profiles
and genuine full-history integrability. -/
theorem weightedFunction_memLp {c : Domain → ℝ} (hc : Measurable c) {M : ℝ}
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (i : Fin n) :
    MemLp (weightedFunction σ target center c i) 2 (historyMeasure q) := by
  have hrow := realHistory_square_product_integrable σ target center hages (basisCoeff i) q
  simp_rw [realHistory_basisCoeff] at hrow
  have hm := weightedFunction_measurable σ target center hc i
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (hrow.const_mul M).mono' ((hm.norm.pow_const (2 : ℕ)).aestronglyMeasurable)
  filter_upwards with p
  have he : ‖‖weightedFunction σ target center c i p‖ ^ 2‖ =
      c p * stoppedRow σ target center p i ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs,
      weightedFunction_square σ target center (fun p => (hcb p).1)]
  rw [he]
  exact mul_le_mul_of_nonneg_right (hcb p).2 (sq_nonneg _)

def weightedFeature (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (i : Fin n) : Lp ℝ 2 (historyMeasure q) :=
  (weightedFunction_memLp σ target center hc hcb hages q i).toLp
    (weightedFunction σ target center c i)

theorem weightedFeature_ae (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (i : Fin n) :
    weightedFeature σ target center c hc M hcb hages q i =ᵐ[historyMeasure q]
      weightedFunction σ target center c i :=
  (weightedFunction_memLp σ target center hc hcb hages q i).coeFn_toLp

/-- The genuine individually stopped covariance, expressed as the actual
time-space integral with separate stopping indicators in every coordinate. -/
def stoppedCovariance (c : Domain → ℝ) (q : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ p, c p * stoppedRow σ target center p i *
    stoppedRow σ target center p j ∂historyMeasure q

/-- This physical covariance is literally the real Gram of actual weighted
L² features, including singular ranks and coincident observations. -/
theorem weightedFeature_gram (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i) (q : ℝ) :
    Matrix.gram ℝ (weightedFeature σ target center c hc M hcb hages q) =
      stoppedCovariance σ target center c q := by
  ext i j
  rw [Matrix.gram_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedFeature_ae σ target center c hc M hcb hages q i,
    weightedFeature_ae σ target center c hc M hcb hages q j] with p hi hj
  rw [hi, hj]
  simp only [RCLike.inner_apply, conj_trivial, weightedFunction]
  calc
    _ = Real.sqrt (c p) ^ 2 * stoppedRow σ target center p i *
        stoppedRow σ target center p j := by ring
    _ = _ := by rw [Real.sq_sqrt (hcb p).1]

theorem weightedSynthesis_ae (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (z : State n) :
    featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z =ᵐ[historyMeasure q]
      (fun p => Real.sqrt (c p) * realHistory σ target center z p) := by
  let v := weightedFeature σ target center c hc M hcb hages q
  have ht (i : Fin n) : (z i • v i : Lp ℝ 2 (historyMeasure q)) =ᵐ[historyMeasure q]
      (fun p => z i * weightedFunction σ target center c i p) := by
    filter_upwards [Lp.coeFn_smul (z i) (v i),
      weightedFeature_ae σ target center c hc M hcb hages q i] with p hp hv
    rw [hp, Pi.smul_apply, smul_eq_mul, hv]
  filter_upwards [Lp.coeFn_fun_finsetSum univ (fun i => z i • v i), ae_all_iff.mpr ht] with p hp ht
  change (∑ i, z i • v i : Lp ℝ 2 (historyMeasure q)) p = _
  rw [hp]
  simp_rw [ht]
  unfold weightedFunction realHistory
  rw [mul_sum]
  exact sum_congr rfl (fun i _ => by ring)

/-- The actual weighted real Gaussian synthesis norm is exactly the signed
physical full-history quadratic energy. -/
theorem weightedSynthesis_norm_sq (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (z : State n) :
    ‖featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z‖ ^ 2 =
      ∫ p, c p * realHistory σ target center z p ^ 2 ∂historyMeasure q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedSynthesis_ae σ target center c hc M hcb hages q z] with p hp
  rw [hp]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    _ = Real.sqrt (c p) ^ 2 * realHistory σ target center z p ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (hcb p).1]

theorem weightedHistory_integrable (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    (q : ℝ) (z : State n) :
    Integrable (fun p => c p * realHistory σ target center z p ^ 2) (historyMeasure q) := by
  let f := featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  apply hi.congr
  filter_upwards [weightedSynthesis_ae σ target center c hc M hcb hages q z] with p hp
  change ‖f p‖ ^ 2 = _
  rw [hp, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hcb p).1]

/-- Ellipticity bounds the genuine weighted stopped covariance against the
entire original undamped full history. No such Gram domination is assumed. -/
theorem weightedSynthesis_full_history_bounds (c : Domain → ℝ) (hc : Measurable c) (M : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M) (hages : ∀ i, σ i ≤ target i)
    {ell : ℝ} (hcl : ∀ p, ell ≤ c p) (q : ℝ) (z : State n) :
    ell * (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target center) q).toReal ≤
      ‖featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z‖ ^ 2 ∧
    ‖featureSynthesis (weightedFeature σ target center c hc M hcb hages q) z‖ ^ 2 ≤
      M * (fullPhysicalEnergy (historyF univ (fun i => (z i : ℂ)) σ target center) q).toReal := by
  rw [weightedSynthesis_norm_sq σ target center c hc M hcb hages q z,
    ← realHistory_full_energy σ target center hages z q,
    ← integral_const_mul, ← integral_const_mul]
  have hu := realHistory_square_product_integrable σ target center hages z q
  have hw := weightedHistory_integrable σ target center c hc M hcb hages q z
  constructor
  · exact integral_mono (hu.const_mul ell) hw
      (fun p => mul_le_mul_of_nonneg_right (hcl p) (sq_nonneg _))
  · exact integral_mono hw (hu.const_mul M)
      (fun p => mul_le_mul_of_nonneg_right (hcb p).2 (sq_nonneg _))

end SHE.StoppedGaussianFeatures
