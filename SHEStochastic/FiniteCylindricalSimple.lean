module

public import SHEStochastic.FiniteCylindricalTerminalIto
public import SHEStochastic.FiniteScalarContinuousModification
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.FiniteCylindricalIto
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
variable {Ω ι C : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- Only finitely many noise coordinates, with bounded predictable simple
coefficients in each; these inputs are dense in cylindrical predictable L2. -/
abbrev Simple := ι →₀ FiniteScalarIto.Simple F H

def simpleEmbedding (e : HilbertBasis ι ℝ C) : Simple (ι := ι) (F := F) (H := H) →ₗ[ℝ] Lp C 2 ν := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact Finsupp.lsum ℝ (fun i ↦ (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i)).toLinearMap.comp
    (FiniteScalarIto.embedding F μ H))

theorem simpleEmbedding_single (e : HilbertBasis ι ℝ C) (i : ι) (v : FiniteScalarIto.Simple F H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    simpleEmbedding e (Finsupp.single i v) =
      L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) (FiniteScalarIto.embedding F μ H v) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact Finsupp.lsum_single _ _ _ _

theorem simpleEmbedding_dense (e : HilbertBasis ι ℝ C) :
    DenseRange (simpleEmbedding (F := F) (μ := μ) (H := H) e) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let S := (LinearMap.range (simpleEmbedding (F := F) (μ := μ) (H := H) e)).topologicalClosure
  have hc : IsClosed (S : Set (Lp C 2 ν)) := Submodule.isClosed_topologicalClosure _
  have hunit (i : ι) (f : Lp ℝ 2 ν) : L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i) f ∈ S := by
    refine (FiniteScalarIto.embedding_dense F μ H).induction_on f
      (hc.preimage (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i)).continuous) ?_
    intro v
    apply Submodule.le_topologicalClosure
    exact ⟨Finsupp.single i v, simpleEmbedding_single e i v⟩
  have hall (v : Lp C 2 ν) : v ∈ S := by
    let hs := L2HilbertSum.total ν (ColumnsHilbertSum.unit e) (ColumnsHilbertSum.unit_total e)
    have hsum : HasSum (fun i ↦ L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i)
        (hs.linearIsometryEquiv v i)) v := by
      simpa only [LinearIsometryEquiv.symm_apply_apply] using
        hs.hasSum_linearIsometryEquiv_symm (hs.linearIsometryEquiv v)
    exact hc.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s ↦
      Submodule.sum_mem S (fun i _ ↦ hunit i _))
  change Dense (LinearMap.range (simpleEmbedding (F := F) (μ := μ) (H := H) e) : Set (Lp C 2 ν))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact top_unique (fun v _ ↦ hall v)

variable (P : FiniteScalarIto.Family F μ H ι)

def simpleProcessLM : Simple (ι := ι) (F := F) (H := H) →ₗ[ℝ] (ℝ≥0 → Ω → ℝ) :=
  Finsupp.lsum ℝ (fun i ↦ (FiniteScalarItoProcess.continuousModel P i).process)

def prefixCLM (e : HilbertBasis ι ℝ C) (t : ℝ≥0) : Lp C 2 ν →L[ℝ] Lp ℝ 2 μ :=
  ((lpMeas ℝ ℝ (F t) 2 μ).subtypeL.comp (condExpL2 ℝ ℝ (F.le t))).comp
    (rawIntegral P.toCoordinates e).toContinuousLinearMap

theorem prefixCLM_single (e : HilbertBasis ι ℝ C) (t : ℝ≥0) (i : ι)
    (v : FiniteScalarIto.Simple F H) :
    prefixCLM P e t (simpleEmbedding e (Finsupp.single i v)) =
      FiniteScalarItoProcess.simpleLp P.toCoordinates i v t := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [simpleEmbedding_single]
  change (condExpL2 ℝ ℝ (F.le t)
    (rawIntegral P.toCoordinates e (L2HilbertSum.lift ν (ColumnsHilbertSum.unit e i)
      (FiniteScalarIto.embedding F μ H v))) : Lp ℝ 2 μ) = _
  rw [rawIntegral_unit, ← FiniteScalarItoProcess.prefixCLM_eq_condExpL2,
    FiniteScalarItoProcess.prefixCLM_simple]

theorem simple_representative (e : HilbertBasis ι ℝ C) (v : Simple (ι := ι) (F := F) (H := H))
    (t : ℝ≥0) :
    (prefixCLM P e t (simpleEmbedding e v) : Ω → ℝ) =ᵐ[μ] simpleProcessLM P v t := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero, Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 μ)
  | single i v =>
      rw [prefixCLM_single]
      simp only [simpleProcessLM, Finsupp.lsum_single]
      change _ =ᵐ[μ] FiniteScalarItoProcess.simpleProcess P.toCoordinates i v t
      exact FiniteScalarItoProcess.simpleLp_ae P.toCoordinates i v t
  | add v u hv hu =>
      simp only [map_add, Pi.add_apply]
      exact (Lp.coeFn_add _ _).trans (hv.add hu)

theorem simple_martingale (v : Simple (ι := ι) (F := F) (H := H)) :
    Martingale (simpleProcessLM P v) F μ := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (martingale_zero ℝ F μ)
  | single i v =>
      simp only [simpleProcessLM, Finsupp.lsum_single]
      change Martingale (fun t ω ↦ FiniteScalarItoProcess.simpleProcess P.toCoordinates i v t ω) F μ
      exact FiniteScalarItoProcess.simple_martingale P.toCoordinates i v
  | add v u hv hu => rw [map_add]; exact hv.add hu

theorem simple_continuous (v : Simple (ι := ι) (F := F) (H := H)) (ω : Ω) :
    Continuous (fun t ↦ simpleProcessLM P v t ω) := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero, Pi.zero_apply] using (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ)))
  | single i v =>
      simpa only [simpleProcessLM, Finsupp.lsum_single] using
        (FiniteScalarItoProcess.continuousModel P i).continuous v ω
  | add v u hv hu =>
      simp only [map_add, Pi.add_apply]
      change Continuous ((fun t ↦ simpleProcessLM P v t ω) + (fun t ↦ simpleProcessLM P u t ω))
      exact hv.add hu

def continuousModel (e : HilbertBasis ι ℝ C) : ContinuousMartingaleExtension.Model
    (Lp C 2 ν) (Simple (ι := ι) (F := F) (H := H)) F μ H where
  embedding := simpleEmbedding e
  dense := simpleEmbedding_dense e
  process := simpleProcessLM P
  martingale := simple_martingale P
  continuous := simple_continuous P
  atTime := prefixCLM P e
  representative := simple_representative P e
  terminal_bound v := by
    change ‖(condExpL2 ℝ ℝ (F.le H) (rawIntegral P.toCoordinates e (simpleEmbedding e v)) : Lp ℝ 2 μ)‖ ≤ _
    exact (norm_condExpL2_coe_le (F.le H) _).trans_eq ((rawIntegral P.toCoordinates e).norm_map _)

theorem exists_continuous_modification (e : HilbertBasis ι ℝ C) (v : Lp C 2 ν) :
    ∃ X : ℝ≥0 → Ω → ℝ, (∀ t, t ≤ H → X t =ᵐ[μ] prefixCLM P e t v) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 H)) :=
  (continuousModel P e).exists_continuous_modification v

end SHEStochastic.FiniteCylindricalIto
