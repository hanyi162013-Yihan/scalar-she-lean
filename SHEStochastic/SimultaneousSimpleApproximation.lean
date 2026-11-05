module

public import SHEStochastic.HilbertSimpleInputs
public import Mathlib.Topology.Sequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SimultaneousSimpleApproximation
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure η] {H : ℝ≥0}

def mixture (μ η : Measure Ω) : Measure Ω := (2 : ℝ≥0∞)⁻¹ • (μ + η)

instance probability_mixture : IsProbabilityMeasure (mixture μ η) := by
  constructor
  simp only [mixture, Measure.smul_apply, Measure.add_apply, measure_univ]
  change (2 : ℝ≥0∞)⁻¹ * (1 + 1) = 1
  norm_num only [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

local notation "νμ" => FiniteScalarIto.inputMeasure F μ H
local notation "νη" => FiniteScalarIto.inputMeasure F η H
local notation "νρ" => FiniteScalarIto.inputMeasure F (mixture μ η) H

theorem input_mixture : νρ = (2 : ℝ≥0∞)⁻¹ • (νμ + νη) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change ((MathFin.ItoIntegralCLM.timeMeasure_T H).prod (mixture μ η)).trim F.predictable_le_prod =
    (2 : ℝ≥0∞)⁻¹ • (((MathFin.ItoIntegralCLM.timeMeasure_T H).prod μ).trim F.predictable_le_prod +
      ((MathFin.ItoIntegralCLM.timeMeasure_T H).prod η).trim F.predictable_le_prod)
  ext s hs
  rw [trim_measurableSet_eq F.predictable_le_prod hs, Measure.smul_apply, Measure.add_apply,
    trim_measurableSet_eq F.predictable_le_prod hs, trim_measurableSet_eq F.predictable_le_prod hs,
    mixture, Measure.prod_smul_right, Measure.prod_add, Measure.smul_apply, Measure.add_apply]

theorem input_twice_mixture : (2 : ℝ≥0∞) • νρ = νμ + νη := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  rw [input_mixture, smul_smul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul]

theorem input_left_le : νμ ≤ (2 : ℝ≥0∞) • νρ := by
  rw [input_twice_mixture]
  exact Measure.le_add_right le_rfl

theorem input_right_le : νη ≤ (2 : ℝ≥0∞) • νρ := by
  rw [input_twice_mixture]
  exact Measure.le_add_left le_rfl

def projectLeft : Lp C 2 νρ →L[ℝ] Lp C 2 νμ :=
  Lp.LpToLpOfMeasureLeSMul (c := 2) (by simp) input_left_le

def projectRight : Lp C 2 νρ →L[ℝ] Lp C 2 νη :=
  Lp.LpToLpOfMeasureLeSMul (c := 2) (by simp) input_right_le

theorem projectLeft_ae (v : Lp C 2 νρ) : projectLeft v =ᵐ[νμ] v :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 2) (by simp) input_left_le v

theorem projectRight_ae (v : Lp C 2 νρ) : projectRight v =ᵐ[νη] v :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 2) (by simp) input_right_le v

theorem projectLeft_embedding (V : HilbertSimpleInputs.bounded (E := C) F H) :
    projectLeft (HilbertSimpleInputs.embedding F (mixture μ η) H V) =
      HilbertSimpleInputs.embedding F μ H V := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  have hac : νμ ≪ νρ := Measure.absolutelyContinuous_of_le_smul input_left_le
  exact (projectLeft_ae _).trans
    ((hac.ae_eq (HilbertSimpleInputs.embedding_ae F (mixture μ η) H V)).trans
      (HilbertSimpleInputs.embedding_ae F μ H V).symm)

theorem projectRight_embedding (V : HilbertSimpleInputs.bounded (E := C) F H) :
    projectRight (HilbertSimpleInputs.embedding F (mixture μ η) H V) =
      HilbertSimpleInputs.embedding F η H V := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  have hac : νη ≪ νρ := Measure.absolutelyContinuous_of_le_smul input_right_le
  exact (projectRight_ae _).trans
    ((hac.ae_eq (HilbertSimpleInputs.embedding_ae F (mixture μ η) H V)).trans
      (HilbertSimpleInputs.embedding_ae F η H V).symm)

theorem projectLeft_cylindrical {ι : Type*} [Countable ι] [DecidableEq ι]
    (e : HilbertBasis ι ℝ C) (V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
    projectLeft (FiniteCylindricalIto.simpleEmbedding (μ := mixture μ η) e V) =
      FiniteCylindricalIto.simpleEmbedding (μ := μ) e V := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  induction V using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add V W hV hW => simp only [map_add, hV, hW]
  | single i v =>
    simp only [FiniteCylindricalIto.simpleEmbedding_single]
    have hac : νμ ≪ νρ := Measure.absolutelyContinuous_of_le_smul input_left_le
    apply Lp.ext
    have hρ := L2HilbertSum.lift_ae νρ (ColumnsHilbertSum.unit e i)
      (FiniteScalarIto.embedding F (mixture μ η) H v)
    have hμ := L2HilbertSum.lift_ae νμ (ColumnsHilbertSum.unit e i)
      (FiniteScalarIto.embedding F μ H v)
    filter_upwards [projectLeft_ae (C := C) (F := F) (μ := μ) (η := η) (H := H) _, hac.ae_eq hρ, hμ,
      hac.ae_eq (HilbertSimpleInputs.embedding_ae F (mixture μ η) H v),
      HilbertSimpleInputs.embedding_ae F μ H v] with p hp hρp hμp hrv hmv
    rw [hp, hρp, hμp]
    exact congrArg (ColumnsHilbertSum.unit e i) (hrv.trans hmv.symm)

theorem projectRight_cylindrical {ι : Type*} [Countable ι] [DecidableEq ι]
    (e : HilbertBasis ι ℝ C) (V : FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H)) :
    projectRight (FiniteCylindricalIto.simpleEmbedding (μ := mixture μ η) e V) =
      FiniteCylindricalIto.simpleEmbedding (μ := η) e V := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  induction V using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add V W hV hW => simp only [map_add, hV, hW]
  | single i v =>
    simp only [FiniteCylindricalIto.simpleEmbedding_single]
    have hac : νη ≪ νρ := Measure.absolutelyContinuous_of_le_smul input_right_le
    apply Lp.ext
    have hρ := L2HilbertSum.lift_ae νρ (ColumnsHilbertSum.unit e i)
      (FiniteScalarIto.embedding F (mixture μ η) H v)
    have hη := L2HilbertSum.lift_ae νη (ColumnsHilbertSum.unit e i)
      (FiniteScalarIto.embedding F η H v)
    filter_upwards [projectRight_ae (C := C) (F := F) (μ := μ) (η := η) (H := H) _, hac.ae_eq hρ, hη,
      hac.ae_eq (HilbertSimpleInputs.embedding_ae F (mixture μ η) H v),
      HilbertSimpleInputs.embedding_ae F η H v] with p hp hρp hηp hrv hηv
    rw [hp, hρp, hηp]
    exact congrArg (ColumnsHilbertSum.unit e i) (hrv.trans hηv.symm)

/-- One bounded predictable simple sequence approximates the same row
in both probability measures. The existing density theorem is applied
once, to their averaged probability; existing change-of-measure CLMs
then give both convergences. -/
theorem exists_sequence {ι : Type*} [Countable ι] [DecidableEq ι] (e : HilbertBasis ι ℝ C)
    (f : Lp C 2 νμ) (g : Lp C 2 νη) (hac : η ≪ μ) (he : f =ᵐ[νμ] g) :
    ∃ V : ℕ → FiniteCylindricalIto.Simple (ι := ι) (F := F) (H := H),
      Filter.Tendsto (fun n ↦ FiniteCylindricalIto.simpleEmbedding (μ := μ) e (V n)) Filter.atTop (𝓝 f) ∧
      Filter.Tendsto (fun n ↦ FiniteCylindricalIto.simpleEmbedding (μ := η) e (V n)) Filter.atTop (𝓝 g) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hiac : νη ≪ νμ :=
    ((Measure.AbsolutelyContinuous.refl (MathFin.ItoIntegralCLM.timeMeasure_T H)).prod hac).trim
      F.predictable_le_prod
  have hQ : MemLp (fun p ↦ f p) 2 νη := (memLp_congr_ae (hiac.ae_eq he)).mpr (Lp.memLp g)
  have hρ : MemLp (fun p ↦ f p) 2 νρ := by
    rw [input_mixture]
    exact ((Lp.memLp f).add_measure hQ).smul_measure (by simp)
  let v : Lp C 2 νρ := hρ.toLp f
  have hacL : νμ ≪ νρ := Measure.absolutelyContinuous_of_le_smul input_left_le
  have hacR : νη ≪ νρ := Measure.absolutelyContinuous_of_le_smul input_right_le
  have hL : projectLeft v = f := Lp.ext ((projectLeft_ae v).trans (hacL.ae_eq hρ.coeFn_toLp))
  have hR : projectRight v = g := Lp.ext
    ((projectRight_ae v).trans ((hacR.ae_eq hρ.coeFn_toLp).trans (hiac.ae_eq he)))
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((FiniteCylindricalIto.simpleEmbedding_dense (F := F) (μ := mixture μ η) (H := H) e) v)
  choose V hV using hw
  have hVlim : Filter.Tendsto (fun n ↦ FiniteCylindricalIto.simpleEmbedding (μ := mixture μ η) e (V n))
      Filter.atTop (𝓝 v) := by simpa only [hV] using hlim
  refine ⟨V, ?_, ?_⟩
  · simpa only [Function.comp_def, projectLeft_cylindrical, hL] using (projectLeft.continuous.tendsto v).comp hVlim
  · simpa only [Function.comp_def, projectRight_cylindrical, hR] using (projectRight.continuous.tendsto v).comp hVlim

end SHEStochastic.SimultaneousSimpleApproximation
