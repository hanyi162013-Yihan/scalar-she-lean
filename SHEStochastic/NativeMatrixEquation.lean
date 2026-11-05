module

public import SHEStochastic.MatrixNemytskii
public import SHEStochastic.MatrixConvolutionMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.NativeMatrixEquation
open MeasureTheory SHE SHE.PredictableL2 MatrixNonlinearCoefficient MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (G : Coefficient d)
  (U : ℝ≥0 × Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)

def profile (p : ℝ≥0 × Ω) : Profile d := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MatrixNemytskii.profile G U hU p

def data (p : ℝ≥0 × Ω) : MatrixSquareCoefficient.Data (profile F G U hU p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MatrixNemytskii.data G U hU p

theorem profile_measurable : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun p => (profile F G U hU p.1).value p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MatrixNemytskii.covariance_measurable G U hU

theorem coefficient_measurable : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun p => (data F G U hU p.1).value p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MatrixNemytskii.coefficient_measurable G U hU

theorem coefficient_ae (p : ℝ≥0 × Ω) :
    (data F G U hU p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] fun x => G.value (U p x) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MatrixNemytskii.coefficient_ae G U hU p

def cap : ℝ := (G.bound : ℝ)^2+1
theorem cap_nonneg : 0 ≤ cap G := by unfold cap; positivity

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- The native predictable input is the actual G(U)* heat* test row;
its measurability, square integrability and full Haar transport are proved. -/
def input (t : ℝ≥0) (ht : t ≤ H) (u : Physical (d := d)) :
    Process (E := Input (d := d)) F μ H :=
  NativeMatrixCoefficient.input F μ H (cap G) (cap_nonneg G) (profile F G U hU) (fun _ => le_rfl)
    (data F G U hU) (profile_measurable F G U hU) (coefficient_measurable F G U hU) t ht u

variable (N : FiniteScalarIto.Family F μ H (d × FiniteHaar.HaarNode)) (u₀ : Physical (d := d))

def Equation : Prop := ∀ t (ht : t ≤ H) u,
  (fun ω => inner ℝ u (U (t,ω))) =ᵐ[μ] fun ω => inner ℝ u (VectorHeat.heat (t : ℝ) u₀)+
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
      (input F G U hU μ H t ht u) ω

/-- Every prescribed bounded vector solution admits the actual completed
infinite Haar realization on its original space and filtration. No L2
moment assumption on the solution is needed for this identification. -/
theorem exists_haar_realization (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEq : Equation F G U hU μ H N u₀) :
    ∃ B : FiniteScalarIto.Family F μ H (d × FiniteHaar.HaarNode), ∀ t (ht : t ≤ H),
      (fun ω => U (t,ω)) =ᵐ[μ] fun ω => VectorHeat.heat (t : ℝ) u₀+
        NativeMatrixConvolution.value B (cap G) (cap_nonneg G) (profile F G U hU)
          (fun _ => le_rfl) (profile_measurable F G U hU) t ht ω := by
  obtain ⟨B,hB⟩ := NativeMatrixCoefficient.exists_haar_family F μ H (cap G) (cap_nonneg G)
    (profile F G U hU) (fun _ => le_rfl) (data F G U hU)
    (profile_measurable F G U hU) (coefficient_measurable F G U hU) N hnull
  refine ⟨B,fun t ht => ?_⟩
  apply HilbertLpObservations.ae_eq μ VectorWhiteCoordinates.basis
  intro i
  let u := VectorWhiteCoordinates.basis i
  let Z := NativeMatrixConvolution.value B (cap G) (cap_nonneg G) (profile F G U hU)
    (fun _ => le_rfl) (profile_measurable F G U hU) t ht
  have hb := (innerSL ℝ u).coeFn_compLpL Z
  rw [hB t ht u] at hb
  filter_upwards [hEq t ht u,hb] with ω he hobs
  rw [he,inner_add_right]
  change inner ℝ u (VectorHeat.heat (t : ℝ) u₀)+_ = inner ℝ u (VectorHeat.heat (t : ℝ) u₀)+_
  congr 1

theorem memLp (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEq : Equation F G U hU μ H N u₀) (t : ℝ≥0) (ht : t ≤ H) :
    MemLp (fun ω => U (t,ω)) 2 μ := by
  obtain ⟨B,hB⟩ := exists_haar_realization F G U hU μ H N u₀ hnull hEq
  have hi := (memLp_const (VectorHeat.heat (t : ℝ) u₀) :
    MemLp (fun _ : Ω => VectorHeat.heat (t : ℝ) u₀) 2 μ).add
    (Lp.memLp (NativeMatrixConvolution.value B (cap G) (cap_nonneg G) (profile F G U hU)
      (fun _ => le_rfl) (profile_measurable F G U hU) t ht))
  exact MemLp.ae_eq (hB t ht).symm hi

theorem memLp_dyadic (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEq : Equation F G U hU μ H N u₀) (t : ℝ≥0) (ht : t ≤ H) (k : ℕ) :
    MemLp (fun ω => U (t,ω)) ((2*2^k : ℕ) : ENNReal) μ := by
  obtain ⟨B,hB⟩ := exists_haar_realization F G U hU μ H N u₀ hnull hEq
  exact MemLp.ae_eq (hB t ht).symm
    ((memLp_const (VectorHeat.heat (t : ℝ) u₀) : MemLp
      (fun _ : Ω => VectorHeat.heat (t : ℝ) u₀) ((2*2^k : ℕ) : ENNReal) μ).add
      (MatrixConvolutionMoments.memLp B (cap G) (cap_nonneg G) (profile F G U hU)
        (fun _ => le_rfl) (profile_measurable F G U hU) t ht k))

end SHEStochastic.NativeMatrixEquation
