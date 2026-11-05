module

public import SHEStochastic.MatrixGlobalHaarRestriction
public import SHEStochastic.MatrixUnboundedPathTightness
public import SHEStochastic.TightLawSubsequence
public import SHEStochastic.WeakLimitProbabilityTools
public import SHEStochastic.SeparateCanonicalCompactness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedLawCompactness
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open StoppedPathPasting
open scoped NNReal ENNReal Topology MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (ρ₀ : MatrixLocalBlockChain.L2Law (n := n)) (radii : ℕ → ℝ≥0)
    (S : ∀ m,MatrixGlobalWeakExistence.Solution 1 (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (radii m))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (radii m)) hβ hβ1.le zero_lt_one ρ₀)
    (hS : ∀ m,Nonempty (MatrixGlobalOriginalFourier.Realization (S m)))
    (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)

include hS hH hH0 in
/-- The previously constructed cutoff solutions have tight actual path
laws. No common probability space or uniqueness of cutoff solutions is
assumed. The artificial coefficient bounds disappear from this claim. -/
theorem tight : IsTightMeasureSet (Set.range (fun m =>
    (MatrixGlobalHaarRestriction.law (S m) H).toMeasure)) := by
  let Ξ := fun m => MatrixGlobalHaarRestriction.Space (S m)
  letI (m : ℕ) : MeasurableSpace (Ξ m) :=
    @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) 1)
      inferInstance ((Measure.dirac () : Measure Unit).prod (S m).law.toMeasure)
  let D := fun m => MatrixGlobalHaarRestriction.filtration (S m)
  let μ := fun m => MatrixGlobalHaarRestriction.measure (S m)
  let U := fun m => MatrixGlobalOriginalFourier.state (S m)
  have hU (m : ℕ) : StronglyMeasurable[(D m).predictable] (U m) :=
    MatrixGlobalOriginalFourier.predictable (S m)
  have hc (m : ℕ) := MatrixGlobalOriginalFourier.continuous (S m)
  let ξ : ∀ m,Ξ m → Physical (d := Fin n) := fun m ω => U m (0,ω)
  have hξ (m : ℕ) : Measurable (ξ m) :=
    ((hU m).mono (predictable_le_product (D m))).measurable.comp (measurable_const.prodMk measurable_id)
  have hn (m : ℕ) : NullCompleteFiltration.ContainsNullSets (D m) (μ m) :=
    RandomInitialBrownianFamily.contains_null (Measure.dirac () : Measure Unit) (S m).law.toMeasure
      (MatrixBlockNaturalFiltration.filtration 1)
  choose B he using fun m => MatrixGlobalHaarRestriction.exists_family (S m) (Classical.choice (hS m)) H hH
  exact MatrixUnboundedPathTightness.tight G hG hβ hβ1 ell hell hLower H hH hH0 D μ U hU hc
    radii B hn ξ hξ he ρ₀.val (fun m => MatrixGlobalOriginalFourier.initial_law (S m))

include hS hH hH0 in
/-- Actual cutoff laws have a weakly convergent subsequence and the
limit preserves exactly the prescribed random initial L2 law.
Identifying its unbounded stochastic equation is a separate step. -/
theorem exists_limit : ∃ Q : ProbabilityMeasure (Path H (Physical (d := Fin n))),
    ∃ φ : ℕ → ℕ,StrictMono φ ∧
      Tendsto ((fun m => MatrixGlobalHaarRestriction.law (S m) H) ∘ φ) atTop (𝓝 Q) ∧
      Q.toMeasure.map (fun p => p (origin H))=ρ₀.val.toMeasure := by
  obtain ⟨Q,φ,hφ,hlim⟩ := TightLawSubsequence.exists_limit
    (fun m => MatrixGlobalHaarRestriction.law (S m) H) (tight G hG hβ hβ1 ell hell hLower ρ₀ radii S hS H hH hH0)
  refine ⟨Q,φ,hφ,hlim,?_⟩
  exact (WeakLimitProbabilityTools.hasLaw
    ((fun m => MatrixGlobalHaarRestriction.law (S m) H) ∘ φ) Q hlim
    (fun p => p (origin H)) (continuous_eval_const _) ρ₀.val.toMeasure
    (fun k => ⟨(continuous_eval_const _).measurable.aemeasurable,
      MatrixGlobalHaarRestriction.initial_path_law (S (φ k)) H⟩)).map_eq


local instance completedSigma (m : ℕ) : MeasurableSpace (MatrixGlobalHaarRestriction.Space (S m)) :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) 1)
    inferInstance ((Measure.dirac () : Measure Unit).prod (S m).law.toMeasure)

/-- The actual original-square driver is retained together with each
cutoff state path, on its own completed probability space. -/
def jointLaws (R : ∀ m,MatrixGlobalOriginalFourier.Realization (S m)) (m : ℕ) :
    ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H) :=
  SeparateCanonicalCompactness.laws
    (fun m => MatrixGlobalHaarRestriction.filtration (S m))
    (fun m => MatrixGlobalHaarRestriction.measure (S m)) H (fun m => (R m).family H)
    (fun m t ω => MatrixGlobalOriginalFourier.state (S m) (t,ω))
    (fun m => MatrixGlobalOriginalFourier.continuous (S m)) m

include hH hH0 in
/-- An actual joint cutoff-law limit retains the original Brownian
noise, its independence from the full state history, and the prescribed
initial law. The unbounded nonlinear equation still needs identification. -/
theorem exists_joint_limit (R : ∀ m,MatrixGlobalOriginalFourier.Realization (S m)) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H),∃ φ : ℕ → ℕ,StrictMono φ ∧
      Tendsto (jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R ∘ φ) atTop (𝓝 Q) ∧
      (∀ j (a : Fin j → Fin n×SHE.FiniteHaar.HaarNode),FiniteBrownianLawOn
        (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
        (fun i => CanonicalStateDriverFiltration.coordinate H (a i))
        (fun i k => if a i=a k then 1 else 0)) ∧
      Q.toMeasure.map (fun x => x.1 (origin H))=ρ₀.val.toMeasure := by
  let D := fun m => MatrixGlobalHaarRestriction.filtration (S m)
  let μ := fun m => MatrixGlobalHaarRestriction.measure (S m)
  let U := fun m t ω => MatrixGlobalOriginalFourier.state (S m) (t,ω)
  let hc := fun m => MatrixGlobalOriginalFourier.continuous (S m)
  let P := fun m => (R m).family H
  have ha (m : ℕ) (t : ℝ≥0) : Measurable[D m t] (U m t) :=
    ((show IsStronglyPredictable (D m) (U m) from MatrixGlobalOriginalFourier.predictable (S m)).stronglyAdapted t).measurable
  have ht : IsTightMeasureSet (Set.range (fun m =>
      (μ m).map (NativeContinuousPath.path H (U m) (hc m)))) :=
    tight G hG hβ hβ1 ell hell hLower ρ₀ radii S (fun m => ⟨R m⟩) H hH hH0
  obtain ⟨Q,φ,hφ,hlim,hBrown⟩ := SeparateCanonicalCompactness.exists_limit D μ H P U hc ha ht
  refine ⟨Q,φ,hφ,hlim,hBrown,?_⟩
  exact SeparateCanonicalCompactness.initial_law D μ H P U hc ha ρ₀.val.toMeasure
    (fun m => MatrixGlobalOriginalFourier.initial_law (S m)) Q φ hlim

/-- The whole cutoff family and its limiting law are constructed from
an arbitrary square-integrable initial distribution, with no assumed
weak solution as an input. This does not yet identify the limit equation. -/
theorem exists_cutoff_limit (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H) :
    ∃ S : ∀ m,MatrixGlobalWeakExistence.Solution 1 (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (radii m))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (radii m)) hβ hβ1.le zero_lt_one ρ₀,
      (∀ m,Nonempty (MatrixGlobalOriginalFourier.Realization (S m))) ∧
      ∃ Q : ProbabilityMeasure (Path H (Physical (d := Fin n))),∃ φ : ℕ → ℕ,StrictMono φ ∧
        Tendsto ((fun m => MatrixGlobalHaarRestriction.law (S m) H) ∘ φ) atTop (𝓝 Q) ∧
        Q.toMeasure.map (fun p => p (origin H))=ρ₀.val.toMeasure := by
  choose S hS using fun m => MatrixUnboundedCutoff.exists_solution G hG hβ ell hell hLower hβ1.le (radii m) ρ₀
  exact ⟨S,hS,exists_limit G hG hβ hβ1 ell hell hLower ρ₀ radii S hS H hH hH0⟩

/-- Construct actual cutoff solutions and a joint state/original-noise
subsequential limit, with the prescribed initial law and full-filtration
Brownian property. This is compactness, not yet the unbounded equation. -/
theorem exists_cutoff_joint_limit (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H) :
    ∃ S : ∀ m,MatrixGlobalWeakExistence.Solution 1
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (radii m))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (radii m)) hβ hβ1.le zero_lt_one ρ₀,
      ∃ R : ∀ m,MatrixGlobalOriginalFourier.Realization (S m),
      ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
        (ι := Fin n×SHE.FiniteHaar.HaarNode) H),∃ φ : ℕ → ℕ,StrictMono φ ∧
        Tendsto (jointLaws G hG hβ hβ1 ell hell hLower ρ₀ radii S H R ∘ φ) atTop (𝓝 Q) ∧
        (∀ j (a : Fin j → Fin n×SHE.FiniteHaar.HaarNode),FiniteBrownianLawOn
          (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
          (fun i => CanonicalStateDriverFiltration.coordinate H (a i))
          (fun i k => if a i=a k then 1 else 0)) ∧
        Q.toMeasure.map (fun x => x.1 (origin H))=ρ₀.val.toMeasure := by
  choose S hS using fun m => MatrixUnboundedCutoff.exists_solution G hG hβ ell hell hLower hβ1.le (radii m) ρ₀
  let R := fun m => Classical.choice (hS m)
  exact ⟨S,R,exists_joint_limit G hG hβ hβ1 ell hell hLower ρ₀ radii S H hH hH0 R⟩

end SHEStochastic.MatrixUnboundedLawCompactness
