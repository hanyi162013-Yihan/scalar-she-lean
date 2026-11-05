module

public import SHEStochastic.MatrixUnboundedLawCompactness
public import SHEStochastic.MatrixUnboundedPathEnergy
public import SHEStochastic.CanonicalBundleEnergy
public import SHEStochastic.UniformEnergyBound
public import SHEStochastic.WeakLimitUniformEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedLawEnergy
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal Topology MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (radii : ℕ → ℝ≥0)
    (S : ∀ m,MatrixGlobalWeakExistence.Solution 1
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (radii m))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (radii m)) hβ hβ1.le zero_lt_one ρ₀)
    (R : ∀ m,MatrixGlobalOriginalFourier.Realization (S m))
    (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)
local instance completedSigma (m : ℕ) : MeasurableSpace (MatrixGlobalHaarRestriction.Space (S m)) :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) 1)
    inferInstance ((Measure.dirac () : Measure Unit).prod (S m).law.toMeasure)

include hH hH0 in
theorem tight : IsTightMeasureSet (Set.range (fun m =>
    (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R m).toMeasure)) := by
  let D := fun m => MatrixGlobalHaarRestriction.filtration (S m)
  let μ := fun m => MatrixGlobalHaarRestriction.measure (S m)
  let U := fun m t ω => MatrixGlobalOriginalFourier.state (S m) (t,ω)
  have ha (m : ℕ) (t : ℝ≥0) : Measurable[D m t] (U m t) :=
    ((show IsStronglyPredictable (D m) (U m) from MatrixGlobalOriginalFourier.predictable (S m)).stronglyAdapted t).measurable
  exact SeparateCanonicalCompactness.tight D μ H (fun m => (R m).family H) U
    (fun m => MatrixGlobalOriginalFourier.continuous (S m)) ha
    (MatrixUnboundedLawCompactness.tight G hG hβ hβ1 ell hell hLower ρ₀ radii S (fun m => ⟨R m⟩) H hH hH0)

include hH hH0 in
/-- The ACTUAL joint cutoff laws have uniformly integrable full
state-path energy. This retains their original-square Brownian driver. -/
theorem uniform_tails :
    Tendsto (fun N : ℕ => ⨆ m,∫⁻ x in {x | (N : ℝ)≤‖x.1‖^2},ENNReal.ofReal (‖x.1‖^2)
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R m).toMeasure)
      atTop (𝓝 0) := by
  let D := fun m => MatrixGlobalHaarRestriction.filtration (S m)
  let μ := fun m => MatrixGlobalHaarRestriction.measure (S m)
  let U := fun m => MatrixGlobalOriginalFourier.state (S m)
  have hU (m : ℕ) : StronglyMeasurable[(D m).predictable] (U m) :=
    MatrixGlobalOriginalFourier.predictable (S m)
  have hc (m : ℕ) := MatrixGlobalOriginalFourier.continuous (S m)
  let ξ := fun m ω => U m (0,ω)
  have hξ (m : ℕ) : Measurable (ξ m) :=
    ((hU m).mono (predictable_le_product (D m))).measurable.comp (measurable_const.prodMk measurable_id)
  have hn (m : ℕ) : NullCompleteFiltration.ContainsNullSets (D m) (μ m) :=
    RandomInitialBrownianFamily.contains_null (Measure.dirac () : Measure Unit) (S m).law.toMeasure
      (MatrixBlockNaturalFiltration.filtration 1)
  choose B he using fun m => MatrixGlobalHaarRestriction.exists_family (S m) (R m) H hH
  have hUI := MatrixUnboundedPathEnergy.uniform_tails G hG hβ hβ1 ell hell hLower H hH hH0
    D μ U hU hc radii B hn ξ hξ he ρ₀.val ρ₀.property
    (fun m => MatrixGlobalOriginalFourier.initial_law (S m))
  apply hUI.congr
  intro N
  apply iSup_congr
  intro m
  have ha (t : ℝ≥0) : Measurable[D m t] (fun ω => U m (t,ω)) :=
    ((show IsStronglyPredictable (D m) (fun t ω => U m (t,ω)) from hU m).stronglyAdapted t).measurable
  exact (CanonicalBundleEnergy.tail (D m) (μ m) H ((R m).family H)
    (fun t ω => U m (t,ω)) (hc m) ha N).symm

include hH hH0 in
/-- A common full path-energy expectation follows from the preceding
actual uniform tails; it is independent of the cutoff cap. -/
theorem expectation_bounds : ∃ A : ℝ,0≤A ∧ ∀ m,
    Integrable (fun x => ‖x.1‖^2)
      (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R m).toMeasure ∧
    (∫ x,‖x.1‖^2 ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
      ρ₀ radii S H R m).toMeasure)≤A :=
  UniformEnergyBound.exists_bound
    (fun m => (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R m).toMeasure)
    (fun _ x => ‖x.1‖^2) (fun _ => by fun_prop) (fun _ _ => sq_nonneg _)
    (uniform_tails G hG hβ hβ1 ell hell hLower ρ₀ radii S R H hH hH0)

include hH hH0 in
/-- Every actual joint weak limit has finite full state-path energy. -/
theorem limit_energy
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H)) (φ : ℕ → ℕ)
    (hP : Tendsto (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R ∘ φ)
      atTop (𝓝 Q)) : Integrable (fun x => ‖x.1‖^2) Q.toMeasure := by
  obtain ⟨A,_,hA⟩ := expectation_bounds G hG hβ hβ1 ell hell hLower ρ₀ radii S R H hH hH0
  exact (WeakLimitMomentTests.nonnegative_bound
    (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R ∘ φ) Q hP
    (fun x => ‖x.1‖^2) (continuous_fst.norm.pow 2) (fun _ => sq_nonneg _) A
    (fun m => (hA (φ m)).1) (fun m => (hA (φ m)).2)).1

include hH hH0 in
/-- Tightness and energy tails are retained by every selected subsequence. -/
theorem tight_subsequence (φ : ℕ → ℕ) : IsTightMeasureSet (Set.range (fun m =>
    (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R (φ m)).toMeasure)) :=
  (tight G hG hβ hβ1 ell hell hLower ρ₀ radii S R H hH hH0).subset
    (by rintro _ ⟨m,rfl⟩;exact Set.mem_range_self (φ m))

include hH hH0 in
theorem uniform_tails_subsequence (φ : ℕ → ℕ) :
    Tendsto (fun N : ℕ => ⨆ m,∫⁻ x in {x | (N : ℝ)≤‖x.1‖^2},ENNReal.ofReal (‖x.1‖^2)
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R (φ m)).toMeasure)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (uniform_tails G hG hβ hβ1 ell hell hLower ρ₀ radii S R H hH hH0) (fun _ => bot_le)
  intro N
  apply iSup_le
  intro m
  exact le_iSup (fun j => ∫⁻ x in {x | (N : ℝ)≤‖x.1‖^2},ENNReal.ofReal (‖x.1‖^2)
    ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R j).toMeasure) (φ m)

include hH hH0 in
/-- Actual joint-law subsequential limits admit all continuous moving
tests with common linear full-path-energy growth. -/
theorem integral_tendsto
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H)) (φ : ℕ → ℕ)
    (hP : Tendsto (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R ∘ φ)
      atTop (𝓝 Q))
    (f : ℕ → CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H → ℝ) (hf : ∀ m,Continuous (f m))
    (g : CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H → ℝ) (hg : Continuous g)
    (hlim : ∀ K,IsCompact K → TendstoUniformlyOn f g atTop K)
    (A : ℝ) (hA : 0≤A) (hfbound : ∀ m x,|f m x|≤A*(1+‖x.1‖^2))
    (hgbound : ∀ x,|g x|≤A*(1+‖x.1‖^2)) :
    Integrable g Q.toMeasure ∧ Tendsto
      (fun m => ∫ x,f m x ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
        ρ₀ radii S H R (φ m)).toMeasure) atTop (𝓝 (∫ x,g x ∂Q.toMeasure)) := by
  let P := MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R
  have ht : IsTightMeasureSet (Set.range (fun m => (P (φ m)).toMeasure)) :=
    tight_subsequence G hG hβ hβ1 ell hell hLower ρ₀ radii S R H hH hH0 φ
  have hui : Tendsto (fun N : ℕ => ⨆ m,∫⁻ x in {x | (N : ℝ)≤‖x.1‖^2},
      ENNReal.ofReal (‖x.1‖^2) ∂(P (φ m)).toMeasure) atTop (𝓝 0) := by
    exact uniform_tails_subsequence G hG hβ hβ1 ell hell hLower ρ₀ radii S R H hH hH0 φ
  exact (WeakLimitUniformEnergy.integral_tendsto (P ∘ φ) Q hP ht (fun x => ‖x.1‖^2)
    (continuous_fst.norm.pow 2) (fun _ => sq_nonneg _) hui f hf g hg hlim A hA hfbound hgbound).2

end SHEStochastic.MatrixUnboundedLawEnergy
