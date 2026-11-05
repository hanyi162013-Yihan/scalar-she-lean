module

public import SHEStochastic.MatrixUnboundedLawEnergy
public import SHEStochastic.MatrixUnboundedCompensatorGrowth
public import SHEStochastic.MatrixUnboundedSquareClosure
public import SHEStochastic.MatrixUnboundedMixedClosure
public import SHEStochastic.SeparateDriverEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section

namespace SHEStochastic.MatrixUnboundedLimitSquare
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 MatrixInfiniteHaar Matrix MatrixFourierCoordinates
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
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (ρ₀ : MatrixLocalBlockChain.L2Law (n := n))
    (S : ∀ m : ℕ,MatrixGlobalWeakExistence.Solution 1
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1.le zero_lt_one ρ₀)
    (R : ∀ m,MatrixGlobalOriginalFourier.Realization (S m))
    (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)
local instance completedSigma (m : ℕ) : MeasurableSpace (MatrixGlobalHaarRestriction.Space (S m)) :=
  @NullMeasurableSpace.instMeasurableSpace (Unit×MatrixGlobalBlockPath.Space (n := n) 1)
    inferInstance ((Measure.dirac () : Measure Unit).prod (S m).law.toMeasure)
variable (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
      ρ₀ (fun m => (m : ℝ≥0)) S H R ∘ φ) atTop (𝓝 Q))
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
  (ι := Fin n×SHE.FiniteHaar.HaarNode) H
variable (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ)
local notation "M" => CanonicalLinearFluctuation.value (ι := Fin n×SHE.FiniteHaar.HaarNode)
  H (coordinate i a freq) ((freq : ℝ)^2)

/-- The original constructed cutoff equations supply the identities
on their actual joint laws, including the original driver. -/
theorem source_identity (m : ℕ) (s t : ℝ≥0) (hst : s≤t) (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (CompensatedEnergyMartingale.value M (fun q x => MatrixFourierSquareTests.compensator H
        (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
        (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1.le i a freq q x) t x-
      CompensatedEnergyMartingale.value M (fun q x => MatrixFourierSquareTests.compensator H
        (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
        (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1.le i a freq q x) s x)
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
        ρ₀ (fun m => (m : ℝ≥0)) S H R m).toMeasure)=0 := by
  let Dm := MatrixGlobalHaarRestriction.filtration (S m)
  let μ := MatrixGlobalHaarRestriction.measure (S m)
  have hn : NullCompleteFiltration.ContainsNullSets Dm μ :=
    RandomInitialBrownianFamily.contains_null (Measure.dirac () : Measure Unit) (S m).law.toMeasure
      (MatrixBlockNaturalFiltration.filtration 1)
  dsimp only [MatrixUnboundedLawCompactness.jointLaws,SeparateCanonicalCompactness.laws,
    ProbabilityMeasure.map,Measure.toProbabilityMeasure,ProbabilityMeasure.coe_mk]
  have hId := MatrixFourierSquareTests.random_identity Dm μ H
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1.le
      (MatrixGlobalOriginalFourier.state (S m)) (MatrixGlobalOriginalFourier.predictable (S m))
      ((R m).family H) i a freq ((MatrixGlobalBlockPath.state 1 0) ∘ Prod.snd)
      ((R m).equation_all (S m) H) (MatrixGlobalOriginalFourier.continuous (S m)) hn s t hst ψ
  apply Eq.trans ?_ hId
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [CompensatedEnergyMartingale.value,WeakLimitCompensatedProducts.value]
    ring

include hH hH0 hφ hlim in
/-- The ACTUAL original-square cutoff-law limit has the literal
unbounded quadratic Fourier compensator. Only the prescribed initial
L2 law is used, with no assumed fourth moment or unbounded solution. -/
theorem square :
    Martingale (fun t x => (M t x)^2-
      MatrixUnboundedFourierCompensator.square G hG hβ hβ1.le H i a freq t x)
      (CanonicalStateDriverFiltration.filtration H) Q.toMeasure := by
  exact MatrixUnboundedSquareClosure.martingale G hG hβ hβ1.le ell hell hLower H i a freq
    (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower ρ₀ (fun m => (m : ℝ≥0)) S H R ∘ φ)
    Q hlim φ hφ
    (MatrixUnboundedLawEnergy.tight_subsequence G hG hβ hβ1 ell hell hLower ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 φ)
    (MatrixUnboundedLawEnergy.uniform_tails_subsequence G hG hβ hβ1 ell hell hLower ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 φ)
    (fun m s t hst ψ => source_identity G hG hβ hβ1 ell hell hLower ρ₀ S R H i a freq (φ m) s t hst ψ)

theorem source_linear_identity (m : ℕ) (s t : ℝ≥0) (hst : s≤t) (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*(M t x-M s x)
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
        ρ₀ (fun m => (m : ℝ≥0)) S H R m).toMeasure)=0 := by
  let Dm := MatrixGlobalHaarRestriction.filtration (S m)
  let μ := MatrixGlobalHaarRestriction.measure (S m)
  have hn : NullCompleteFiltration.ContainsNullSets Dm μ :=
    RandomInitialBrownianFamily.contains_null (Measure.dirac () : Measure Unit) (S m).law.toMeasure
      (MatrixBlockNaturalFiltration.filtration 1)
  dsimp only [MatrixUnboundedLawCompactness.jointLaws,SeparateCanonicalCompactness.laws,
    ProbabilityMeasure.map,Measure.toProbabilityMeasure,ProbabilityMeasure.coe_mk]
  exact MatrixFourierPathMoments.random_identity Dm μ H
    (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1.le
    (MatrixGlobalOriginalFourier.state (S m)) (MatrixGlobalOriginalFourier.predictable (S m))
    ((R m).family H) ((MatrixGlobalBlockPath.state 1 0) ∘ Prod.snd)
    ((R m).equation_all (S m) H) (MatrixGlobalOriginalFourier.continuous (S m)) hn i a freq s t hst ψ

include hH hH0 hlim in
theorem memLp (t : ℝ≥0) : MemLp (M t) 2 Q.toMeasure := by
  have hi := MatrixUnboundedLawEnergy.limit_energy G hG hβ hβ1 ell hell hLower
    ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 Q φ hlim
  let K : ℝ := ((Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖)^2
  apply (memLp_two_iff_integrable_sq (CanonicalLinearFluctuation.continuous H
    (coordinate i a freq) ((freq : ℝ)^2) t).aestronglyMeasurable).mpr
  apply (((integrable_const (1 : ℝ)).add hi).const_mul K).mono'
    ((CanonicalLinearFluctuation.continuous H (coordinate i a freq) ((freq : ℝ)^2) t).pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact MatrixUnboundedSquareClosure.fluctuation_bound H i a freq t x

include hH hH0 hlim in
/-- The same actual weak limit has every ordinary linear Fourier
martingale, with square integrability from the full path-energy bound. -/
theorem linear : Martingale M (CanonicalStateDriverFiltration.filtration H) Q.toMeasure := by
  apply BCFL1PastTesting.martingale Q.toMeasure (CanonicalStateDriverFiltration.filtration H)
    (CanonicalStateDriverFiltration.history H) (fun t => (WeakLimitCanonicalBrownian.continuous_history H t).measurable)
    (fun _ => le_rfl) M (CanonicalLinearFluctuation.adapted H (coordinate i a freq) ((freq : ℝ)^2))
    (fun t => (memLp G hG hβ hβ1 ell hell hLower ρ₀ S R H hH hH0 Q φ hlim i a freq t).integrable one_le_two)
  intro s t hst ψ
  let f := fun x : X => ψ (CanonicalStateDriverFiltration.history H s x)*(M t x-M s x)
  have hc : Continuous f := (ψ.continuous.comp (WeakLimitCanonicalBrownian.continuous_history H s)).mul
    ((CanonicalLinearFluctuation.continuous H (coordinate i a freq) ((freq : ℝ)^2) t).sub
      (CanonicalLinearFluctuation.continuous H (coordinate i a freq) ((freq : ℝ)^2) s))
  let B : ℝ := (Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖
  let A : ℝ := 2*‖ψ‖*B
  have hA : 0≤A := by dsimp only [A,B];positivity
  have hb (x : X) : |f x|≤A*(1+‖x.1‖^2) := by
    have hm (q : ℝ≥0) : ‖M q x‖≤B*‖x.1‖ :=
      CanonicalEnergyGrowth.fluctuation H (coordinate i a freq) ((freq : ℝ)^2) (sq_nonneg _) q x
    have hnorm : ‖x.1‖≤1+‖x.1‖^2 := by nlinarith [sq_nonneg (‖x.1‖-1)]
    change |ψ (CanonicalStateDriverFiltration.history H s x)*(M t x-M s x)|≤_
    rw [←Real.norm_eq_abs,norm_mul]
    calc
      _ ≤ ‖ψ‖*(‖M t x‖+‖M s x‖) := mul_le_mul (ψ.norm_coe_le_norm _) (norm_sub_le _ _)
        (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖ψ‖*(B*‖x.1‖+B*‖x.1‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (hm t) (hm s)) (norm_nonneg _)
      _ = A*‖x.1‖ := by dsimp only [A];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hA
  have hconst (K : Set X) (_hK : IsCompact K) : TendstoUniformlyOn (fun _ : ℕ => f) f atTop K := by
    intro V hV
    exact Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hV
  have ht := (MatrixUnboundedLawEnergy.integral_tendsto G hG hβ hβ1 ell hell hLower
    ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 Q φ hlim (fun _ => f) (fun _ => hc) f hc hconst A hA
    (fun _ => hb) hb).2
  have hz : Tendsto (fun m => ∫ x,f x
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
        ρ₀ (fun m => (m : ℝ≥0)) S H R (φ m)).toMeasure) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun m =>
      (source_linear_identity G hG hβ hβ1 ell hell hLower ρ₀ S R H i a freq (φ m) s t hst ψ).symm)
  exact tendsto_nhds_unique ht hz

include hH hH0 in
theorem mixed_energy_tails (k : Fin n×SHE.FiniteHaar.HaarNode) :
    Tendsto (fun N : ℕ => ⨆ m,∫⁻ x in {x | (N : ℝ)≤MatrixUnboundedMixedClosure.energy H k x},
      ENNReal.ofReal (MatrixUnboundedMixedClosure.energy H k x)
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
        ρ₀ (fun m => (m : ℝ≥0)) S H R (φ m)).toMeasure) atTop (𝓝 0) := by
  let D := fun m => MatrixGlobalHaarRestriction.filtration (S (φ m))
  let μ := fun m => MatrixGlobalHaarRestriction.measure (S (φ m))
  let U := fun m t ω => MatrixGlobalOriginalFourier.state (S (φ m)) (t,ω)
  have ha (m : ℕ) (t : ℝ≥0) : Measurable[D m t] (U m t) :=
    ((show IsStronglyPredictable (D m) (U m) from
      MatrixGlobalOriginalFourier.predictable (S (φ m))).stronglyAdapted t).measurable
  have hd := SeparateDriverEnergy.path_uniform_tails D μ H (fun m => (R (φ m)).family H) U
    (fun m => MatrixGlobalOriginalFourier.continuous (S (φ m))) ha MatrixPredictableHaarRotation.basis k
  have hs := MatrixUnboundedLawEnergy.uniform_tails_subsequence G hG hβ hβ1 ell hell hLower
    ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 φ
  exact EnergyTailAddition.uniform_tails
    (fun m => (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
      ρ₀ (fun m => (m : ℝ≥0)) S H R (φ m)).toMeasure)
    (fun _ x => ‖x.1‖^2) (fun _ x => ‖x.2 k‖^2)
    (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _) hs hd

theorem source_mixed_identity (m : ℕ) (k : Fin n×SHE.FiniteHaar.HaarNode)
    (s t : ℝ≥0) (hst : s≤t) (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (CompensatedEnergyMartingale.productValue M (CanonicalStateDriverFiltration.coordinate H k)
        (fun q x => MatrixUnboundedMixedClosure.cutoff G hG hβ hβ1.le ell hell hLower H i a freq k m q x) t x-
      CompensatedEnergyMartingale.productValue M (CanonicalStateDriverFiltration.coordinate H k)
        (fun q x => MatrixUnboundedMixedClosure.cutoff G hG hβ hβ1.le ell hell hLower H i a freq k m q x) s x)
      ∂(MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
        ρ₀ (fun m => (m : ℝ≥0)) S H R m).toMeasure)=0 := by
  let Dm := MatrixGlobalHaarRestriction.filtration (S m)
  let μ := MatrixGlobalHaarRestriction.measure (S m)
  have hn : NullCompleteFiltration.ContainsNullSets Dm μ :=
    RandomInitialBrownianFamily.contains_null (Measure.dirac () : Measure Unit) (S m).law.toMeasure
      (MatrixBlockNaturalFiltration.filtration 1)
  dsimp only [MatrixUnboundedLawCompactness.jointLaws,SeparateCanonicalCompactness.laws,
    ProbabilityMeasure.map,Measure.toProbabilityMeasure,ProbabilityMeasure.coe_mk]
  simpa only [CompensatedEnergyMartingale.productValue,WeakLimitCompensatedProducts.value,
    MatrixUnboundedMixedClosure.cutoff] using MatrixFourierMixedTests.random_identity Dm μ H
    (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1.le
    (MatrixGlobalOriginalFourier.state (S m)) (MatrixGlobalOriginalFourier.predictable (S m))
    ((R m).family H) i a freq ((MatrixGlobalBlockPath.state 1 0) ∘ Prod.snd)
    ((R m).equation_all (S m) H) (MatrixGlobalOriginalFourier.continuous (S m)) hn k s t hst ψ

include hH hH0 hφ hlim in
/-- The actual unbounded joint weak limit retains every mixed Fourier
state/original-driver characteristic. Its full driver, not only its
state covariance, is identified. -/
theorem mixed (k : Fin n×SHE.FiniteHaar.HaarNode) :
    Martingale (fun t x => M t x*CanonicalStateDriverFiltration.coordinate H k t x-
      MatrixUnboundedFourierCompensator.mixed G hG hβ hβ1.le H i a freq k t x)
      (CanonicalStateDriverFiltration.filtration H) Q.toMeasure :=
  MatrixUnboundedMixedClosure.martingale G hG hβ hβ1.le ell hell hLower H i a freq k
    (MatrixUnboundedLawCompactness.jointLaws G hG hβ hβ1 ell hell hLower
      ρ₀ (fun m => (m : ℝ≥0)) S H R ∘ φ) Q hlim φ hφ
    (MatrixUnboundedLawEnergy.tight_subsequence G hG hβ hβ1 ell hell hLower
      ρ₀ (fun m => (m : ℝ≥0)) S R H hH hH0 φ)
    (mixed_energy_tails G hG hβ hβ1 ell hell hLower ρ₀ S R H hH hH0 φ k)
    (fun m s t hst ψ => source_mixed_identity G hG hβ hβ1 ell hell hLower ρ₀ S R H i a freq (φ m) k s t hst ψ)

end SHEStochastic.MatrixUnboundedLimitSquare
