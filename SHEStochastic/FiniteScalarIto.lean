/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Finite-horizon assembly adapts the simple-process/density construction of
formal-mathfin, 3c41aee9bf2d9743f9e66b439f90d1635843d2d2. Its deterministic
embedding and density proofs are reused from FilteredItoCLM. All stochastic
pairings now come from the manuscript's recognized finite-horizon laws.
-/
module

public import SHEStochastic.FiniteBrownianPairing
public import SHEStochastic.FilteredScalarIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.FiniteScalarIto
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal InnerProductSpace

/-- Terminal integration needs adapted coordinates and their finite
Brownian laws. Path continuity is used separately for continuous versions. -/
structure Coordinates {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0) (ι : Type*) [DecidableEq ι] where
  W : ι → ℝ≥0 → Ω → ℝ
  adapted : ∀ i t, Measurable[F t] (W i t)
  law : ∀ n (a : Fin n → ι), FiniteBrownianLawOn F μ H (fun i ↦ W (a i))
    (fun i j ↦ if a i = a j then 1 else 0)

structure Family {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0) (ι : Type*) [DecidableEq ι]
    extends Coordinates F μ H ι where
  continuous : ∀ i ω, Continuous (fun t ↦ W i t ω)

instance {Ω : Type*} [MeasurableSpace Ω] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {μ : Measure Ω} {H : ℝ≥0} {ι : Type*} [DecidableEq ι] :
    CoeOut (Family F μ H ι) (Coordinates F μ H ι) := ⟨Family.toCoordinates⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

abbrev Simple (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0) :=
  FilteredItoCLM.TBoundedSP (𝓖 := F) H (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)

def inputMeasure (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0) :=
  FilteredItoCLM.trimMeasure_T (𝓖 := F) (μ := μ) H
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)

def embedding (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    Simple F H →ₗ[ℝ] Lp ℝ 2 (inputMeasure F μ H) :=
  FilteredItoCLM.simpleAssembly_T (𝓖 := F) (μ := μ) H
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)

theorem embedding_dense (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    DenseRange (embedding F μ H) :=
  FilteredItoCLM.simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) H
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)

variable (P : Coordinates F μ H ι)

theorem measurable_coordinate (i : ι) : ∀ t, Measurable (P.W i t) :=
  fun t ↦ (P.adapted i t).mono (F.le t) le_rfl

def simpleValue (i : ι) (V : Simple F H) : Ω → ℝ :=
  FilteredItoL2.itoSimple (measurable_coordinate P i) V.val

theorem memLp_term (i : ι) (V : Simple F H) (p : ℝ≥0 × ℝ≥0) (hp : p ∈ V.val.value.support) :
    MemLp (fun ω ↦ V.val.value p ω * (P.W i p.2 ω - P.W i p.1 ω)) 2 μ := by
  apply BrownianCoordinates.memLp_adapted_mul_increment F μ H P.W P.law i p.1 p.2
    (V.val.le_of_mem_support_value p hp) (V.property p hp) (V.val.measurable_value p)
  exact MemLp.of_bound ((V.val.measurable_value p).mono (F.le p.1) le_rfl).aestronglyMeasurable
    V.val.valueBound (Filter.Eventually.of_forall (V.val.value_le_valueBound p))

theorem memLp_simpleValue (i : ι) (V : Simple F H) : MemLp (simpleValue P i V) 2 μ := by
  change MemLp (fun ω ↦ ∑ p ∈ V.val.value.support,
    V.val.value p ω * (P.W i p.2 ω - P.W i p.1 ω)) 2 μ
  exact memLp_finsetSum _ (fun p hp ↦ memLp_term P i V p hp)

def simpleLp (i : ι) (V : Simple F H) : Lp ℝ 2 μ :=
  (memLp_simpleValue P i V).toLp (simpleValue P i V)

/-- Mixed scalar-coordinate isometry on two bounded predictable simple inputs. -/
theorem simple_pairing (i j : ι) (V U : Simple F H) :
    (∫ ω, simpleValue P i V ω * simpleValue P j U ω ∂μ) =
      ∑ p ∈ V.val.value.support, ∑ q ∈ U.val.value.support,
        (∫ ω, V.val.value p ω * U.val.value q ω ∂μ) *
          (max 0 (min (p.2 : ℝ) q.2 - max (p.1 : ℝ) q.1) * (if i = j then 1 else 0)) := by
  let a (p : ℝ≥0 × ℝ≥0) (ω : Ω) := V.val.value p ω * (P.W i p.2 ω - P.W i p.1 ω)
  let b (q : ℝ≥0 × ℝ≥0) (ω : Ω) := U.val.value q ω * (P.W j q.2 ω - P.W j q.1 ω)
  have hint (p) (hp : p ∈ V.val.value.support) (q) (hq : q ∈ U.val.value.support) :
      Integrable (fun ω ↦ a p ω * b q ω) μ :=
    (memLp_term P i V p hp).integrable_mul (memLp_term P j U q hq)
  change (∫ ω, (∑ p ∈ V.val.value.support, a p ω) *
    (∑ q ∈ U.val.value.support, b q ω) ∂μ) = _
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ (fun q hq ↦ hint p hp q hq))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_finsetSum _ (fun q hq ↦ hint p hp q hq)]
  apply Finset.sum_congr rfl
  intro q hq
  exact BrownianCoordinates.rectangle_pairing F μ H P.W P.law P.adapted i j
    (V.val.measurable_value p) (U.val.measurable_value q)
    (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound p ω)
    (fun ω ↦ by rw [← Real.norm_eq_abs]; exact U.val.value_le_valueBound q ω)
    (V.val.le_of_mem_support_value p hp) (U.val.le_of_mem_support_value q hq)
    (V.property p hp) (U.property q hq)

theorem simpleLp_norm (i : ι) (V : Simple F H) : ‖simpleLp P i V‖ = ‖embedding F μ H V‖ := by
  have hsq : ‖simpleLp P i V‖ ^ 2 = ‖embedding F μ H V‖ ^ 2 := by
    have hl : ‖simpleLp P i V‖ ^ 2 = ∫ ω, simpleValue P i V ω ^ 2 ∂μ := by
      rw [MathFin.ItoIntegralL2.lp_two_norm_sq]
      apply integral_congr_ae
      filter_upwards [(memLp_simpleValue P i V).coeFn_toLp] with ω hω
      exact congrArg (fun r : ℝ ↦ r ^ 2) hω
    rw [hl]
    simp only [pow_two]
    rw [simple_pairing P i i V V]
    simp only [ite_true, mul_one]
    rw [← pow_two]
    change _ = ‖FilteredItoCLM.simpleProcessL2_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) V.val‖ ^ 2
    rw [FilteredItoCLM.simpleProcessL2_T_norm_eq (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const) V,
      FilteredItoL2.simpleProcessL2_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem simpleValue_add (i : ι) (V U : Simple F H) :
    simpleValue P i (V + U) = simpleValue P i V + simpleValue P i U := by
  change FilteredItoL2.itoSimple (measurable_coordinate P i) (V + U).val = _
  rw [Submodule.coe_add, FilteredItoL2.itoSimple_add]
  rfl

theorem simpleValue_smul (i : ι) (c : ℝ) (V : Simple F H) :
    simpleValue P i (c • V) = c • simpleValue P i V := by
  change FilteredItoL2.itoSimple (measurable_coordinate P i) (c • V).val = _
  rw [Submodule.coe_smul, FilteredItoL2.itoSimple_smul]
  rfl

def simpleMap (i : ι) : Simple F H →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := simpleLp P i
  map_add' V U := by
    rw [simpleLp, simpleLp, simpleLp,
      ← MemLp.toLp_add (memLp_simpleValue P i V) (memLp_simpleValue P i U)]
    congr 1
    exact simpleValue_add P i V U
  map_smul' c V := by
    rw [simpleLp, simpleLp, RingHom.id_apply,
      ← MemLp.toLp_const_smul c (memLp_simpleValue P i V)]
    congr 1
    exact simpleValue_smul P i c V

def integralCLM (i : ι) : Lp ℝ 2 (inputMeasure F μ H) →L[ℝ] Lp ℝ 2 μ :=
  (simpleMap P i).extendOfNorm (embedding F μ H)

theorem integralCLM_simple (i : ι) (V : Simple F H) :
    integralCLM P i (embedding F μ H V) = simpleLp P i V := by
  rw [integralCLM, LinearMap.extendOfNorm_eq (embedding_dense F μ H)
    ⟨1, fun U ↦ by rw [one_mul]; exact (simpleLp_norm P i U).le⟩]
  rfl

theorem integralCLM_norm (i : ι) (v : Lp ℝ 2 (inputMeasure F μ H)) :
    ‖integralCLM P i v‖ = ‖v‖ := by
  unfold integralCLM
  exact LinearMap.norm_extendOfNorm_eq_of_isometry (embedding_dense F μ H)
    (simpleLp_norm P i) v

/-- The scalar-coordinate Itô isometry from exactly the paper's native
finite-horizon Brownian input. No Brownian law beyond H is used. -/
def rawIsometry (i : ι) : Lp ℝ 2 (inputMeasure F μ H) →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  { (integralCLM P i).toLinearMap with norm_map' := integralCLM_norm P i }

def integral (i : ι) : PredictableL2.Process (E := ℝ) F μ H →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  (rawIsometry P i).comp (FilteredScalarIto.processTransport (𝓖 := F) (μ := μ) H
    (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const))

theorem rawIsometry_simple (i : ι) (V : Simple F H) :
    rawIsometry P i (embedding F μ H V) = simpleLp P i V := integralCLM_simple P i V

theorem simpleLp_orthogonal (i j : ι) (hij : i ≠ j) (V U : Simple F H) :
    inner ℝ (simpleLp P i V) (simpleLp P j U) = 0 := by
  rw [L2.inner_def]
  have he : (∫ ω, inner ℝ (simpleLp P i V ω) (simpleLp P j U ω) ∂μ) =
      ∫ ω, simpleValue P i V ω * simpleValue P j U ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [(memLp_simpleValue P i V).coeFn_toLp,
      (memLp_simpleValue P j U).coeFn_toLp] with ω hv hu
    change simpleLp P i V ω = simpleValue P i V ω at hv
    change simpleLp P j U ω = simpleValue P j U ω at hu
    change simpleLp P j U ω * simpleLp P i V ω = _
    rw [hv, hu]
    ring
  rw [he, simple_pairing P i j V U]
  simp only [if_neg hij, mul_zero, Finset.sum_const_zero]

/-- Coordinate integral ranges are mutually orthogonal even when the
integrands depend on the full common past. Density extends the actual
mixed-coordinate rectangle calculation to every predictable L2 input. -/
theorem orthogonal :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    OrthogonalFamily ℝ (fun _ : ι ↦ Lp ℝ 2 (inputMeasure F μ H)) (rawIsometry P) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  intro i j hij f g
  have hs (V U : Simple F H) :
      inner ℝ (rawIsometry P i (embedding F μ H V))
        (rawIsometry P j (embedding F μ H U)) = 0 := by
    rw [rawIsometry_simple, rawIsometry_simple]
    exact simpleLp_orthogonal P i j hij V U
  have hV (V : Simple F H) (g : Lp ℝ 2 (inputMeasure F μ H)) :
      inner ℝ (rawIsometry P i (embedding F μ H V)) (rawIsometry P j g) = 0 := by
    exact congrFun (DenseRange.equalizer (embedding_dense F μ H)
      (continuous_const.inner (rawIsometry P j).continuous) continuous_const
      (funext fun U ↦ hs V U)) g
  exact congrFun (DenseRange.equalizer (embedding_dense F μ H)
    ((rawIsometry P i).continuous.inner continuous_const) continuous_const
    (funext fun V ↦ hV V g)) f

theorem simpleValue_centered (i : ι) (V : Simple F H) :
    ∫ ω, simpleValue P i V ω ∂μ = 0 := by
  change (∫ ω, ∑ p ∈ V.val.value.support,
    V.val.value p ω * (P.W i p.2 ω - P.W i p.1 ω) ∂μ) = 0
  rw [integral_finsetSum _ (fun p hp ↦ (memLp_term P i V p hp).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro p hp
  exact BrownianCoordinates.integral_adapted_mul_increment F μ H P.W P.law i p.1 p.2
    (V.val.le_of_mem_support_value p hp) (V.property p hp) (V.val.measurable_value p)

theorem simpleLp_centered (i : ι) (V : Simple F H) : ∫ ω, simpleLp P i V ω ∂μ = 0 := by
  exact (integral_congr_ae (memLp_simpleValue P i V).coeFn_toLp).trans (simpleValue_centered P i V)

omit P in
theorem mean_eq_inner (f : Lp ℝ 2 μ) :
    (∫ ω, f ω ∂μ) = inner ℝ (Lp.const 2 μ (1 : ℝ)) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with ω hω
  change f ω = f ω * (Lp.const 2 μ (1 : ℝ)) ω
  rw [hω]
  change f ω = f ω * 1
  rw [mul_one]

theorem rawIsometry_centered (i : ι) (f : Lp ℝ 2 (inputMeasure F μ H)) :
    ∫ ω, rawIsometry P i f ω ∂μ = 0 := by
  rw [mean_eq_inner]
  exact congrFun (DenseRange.equalizer (embedding_dense F μ H)
    (continuous_const.inner (rawIsometry P i).continuous) continuous_const
    (funext fun V ↦ by
      change inner ℝ (Lp.const 2 μ (1 : ℝ)) (rawIsometry P i (embedding F μ H V)) = 0
      rw [rawIsometry_simple, ← mean_eq_inner, simpleLp_centered])) f

theorem integral_centered (i : ι) (v : PredictableL2.Process (E := ℝ) F μ H) :
    ∫ ω, integral P i v ω ∂μ = 0 := rawIsometry_centered P i _

end SHEStochastic.FiniteScalarIto
