module

public import SHEStochastic.NativeEnergy
public import SHEStochastic.NativeSimpleExponential

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeExponential
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open FilteredSimplePartition

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "emb" => HilbertSimpleInputs.embedding F μ H

def density (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) (ω : Ω) : ℝ :=
  Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω - a ^ 2 * NativeEnergy.energy u ω / 2)

theorem density_zero (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) (a : ℝ) :
    density P e a (0 : Lp C 2 νin) =ᵐ[μ] (fun _ ↦ 1) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have he := NativeEnergy.energy_ae_of_ae (0 : Lp C 2 νin) (fun _ ↦ 0)
    (Lp.coeFn_zero C 2 νin)
  have hz : FiniteCylindricalIto.rawIntegral P.toCoordinates e (0 : Lp C 2 νin) = 0 := map_zero _
  filter_upwards [he, Lp.coeFn_zero ℝ 2 μ] with ω hE hI
  simp only [density, hz, hI, hE, Pi.zero_apply, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    integral_zero, mul_zero, zero_div, sub_zero, Real.exp_zero]

theorem stronglyMeasurable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (u : Lp C 2 νin) : StronglyMeasurable (density P e a u) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ Real.exp (a * p.1 - a ^ 2 * p.2 / 2)) := by fun_prop
  exact hc.comp_stronglyMeasurable
    ((Lp.stronglyMeasurable (FiniteCylindricalIto.rawIntegral P.toCoordinates e u)).prodMk
      (NativeEnergy.stronglyMeasurable u))

theorem simple_ae (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (V : HilbertSimpleInputs.bounded (E := C) F H) :
    density P e a (emb V) =ᵐ[μ]
      (fun ω ↦ Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (emb V) ω - a ^ 2 *
        (∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H) / 2)) := by
  filter_upwards [NativeEnergy.energy_ae_of_ae _ _ (HilbertSimpleInputs.embedding_ae F μ H V)]
    with ω hω
  change Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (emb V) ω - a ^ 2 *
    NativeEnergy.energy (emb V) ω / 2) = _
  rw [hω]
  rfl

theorem simple_mean_one (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1) :
    Integrable (density P e a (emb V)) μ ∧ (∫ ω, density P e a (emb V) ω ∂μ) = 1 := by
  obtain ⟨hi, he⟩ := NativeSimpleExponential.mean_one P e V v hv
    ((marshalEndpoints F H V.val).card - 1)
    (marshalPart_card_sub_one F H V.val V.property) a
  have h := simple_ae P e a V
  exact ⟨hi.congr (Filter.EventuallyEq.symm h), (integral_congr_ae h).trans he⟩

theorem simple_square_bound (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (V : HilbertSimpleInputs.bounded (E := C) F H) (v : C) (hv : ‖v‖ = 1)
    (K : ℝ) (hcap : ∀ᵐ ω ∂μ,
      (∫ r, ‖V.val r ω‖ ^ 2 ∂MathFin.ItoIntegralCLM.timeMeasure_T H) ≤ K) :
    MemLp (density P e a (emb V)) 2 μ ∧
      (∫ ω, density P e a (emb V) ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) := by
  obtain ⟨hi, hb⟩ := NativeSimpleExponential.square_integral_le P e V v hv
    ((marshalEndpoints F H V.val).card - 1)
    (marshalPart_card_sub_one F H V.val V.property) a K hcap
  have h := (simple_ae P e a V).mono fun ω hω ↦ congrArg (fun x : ℝ ↦ x ^ 2) hω
  have hi' := hi.congr (Filter.EventuallyEq.symm h)
  exact ⟨(memLp_two_iff_integrable_sq (stronglyMeasurable P e a (emb V)).aestronglyMeasurable).mpr hi',
    (integral_congr_ae h).trans_le hb⟩

end SHEStochastic.NativeExponential
