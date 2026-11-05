module

public import SHEStochastic.MatrixUnboundedFieldLaws
public import SHEStochastic.CoupledLawTightness
public import SHEStochastic.MatrixUnboundedExitTail
public import SHEStochastic.TightnessByLocalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedPathTightness
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open HeatParameterCover HeatParameterCoordinates StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
variable {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)

include hβ1 hH0 in
/-- Actual solutions of the unbounded coefficient's bounded radial
cutoffs have tight original L2 path laws on every short finite horizon.
Only the original Holder constant, sublinear exponent and prescribed
initial law are common. The coefficient bounds may diverge, and each
solution may have its own probability space, filtration and driver. -/
theorem tight {Ξ : ℕ → Type*} [∀ m,MeasurableSpace (Ξ m)]
    (D : ∀ m,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ξ m)))
    (μ : ∀ m,Measure (Ξ m)) [∀ m,IsProbabilityMeasure (μ m)]
    (U : ∀ m,ℝ≥0×Ξ m → Physical (d := Fin n))
    (hU : ∀ m,StronglyMeasurable[(D m).predictable] (U m))
    (hcU : ∀ m ω,Continuous (fun t => U m (t,ω))) (radii : ℕ → ℝ≥0)
    (B : ∀ m,FiniteScalarIto.Family (D m) (μ m) H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : ∀ m,NullCompleteFiltration.ContainsNullSets (D m) (μ m))
    (ξ : ∀ m,Ξ m → Physical (d := Fin n)) (hξ : ∀ m,Measurable (ξ m))
    (hEq : ∀ m,MatrixRandomMildExistence.Equation (G_R (radii m)) hH (B m) (U m) (hU m) (ξ m))
    (ρ : ProbabilityMeasure (Physical (d := Fin n))) (hInitial : ∀ m,(μ m).map (ξ m)=ρ.toMeasure) :
    IsTightMeasureSet (Set.range (fun m => (μ m).map
      (NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hcU m)))) := by
  let W : ∀ K m : ℕ,ℝ≥0×Ξ m → Physical (d := Fin n) := fun (K m : ℕ) => MatrixL2LocalizedPointRows.state (U m) ((K+1 : ℕ) : ℝ≥0)
  have hW (K m : ℕ) : StronglyMeasurable[(D m).predictable] (W K m) :=
    MatrixL2LocalizedPointRows.predictable (D m) (U m) (hU m) ((K+1 : ℕ) : ℝ≥0)
  have hex (K : ℕ) := MatrixUnboundedFieldLaws.exists_tight_versions G hG hβ hβ1 ell hell hLower H hH
    D μ (W K) (hW K) radii B ((K+1 : ℕ) : ℝ)
    (fun m => Filter.Eventually.of_forall (MatrixL2LocalizedPointRows.norm_bound (U m) ((K+1 : ℕ) : ℝ≥0)))
  choose Y hYm hrep hzero hTight using hex
  let Z : ∀ K m,Ξ m → Path H (Physical (d := Fin n)) :=
    fun K m ω => VectorMildPathTightness.path (d := Fin n) H hH0 (ξ m ω) (Y K m ω)
  have hZ (K m : ℕ) : Measurable (Z K m) := by
    dsimp only [Z]
    have hp : Measurable (fun ω : Ξ m => (ξ m ω,Y K m ω)) :=
      (hξ m).prodMk (hYm K m)
    exact Measurable.comp
      (f := fun ω : Ξ m => (ξ m ω,Y K m ω))
      (g := fun z : Physical (d := Fin n)×(Fin n → C(Parameter,ℝ)) =>
        VectorMildPathTightness.path (d := Fin n) H hH0 z.1 z.2)
      (VectorMildPathTightness.continuous_joint (d := Fin n) H hH0).measurable hp
  have htZ (K : ℕ) : IsTightMeasureSet (Set.range (fun m => (μ m).map (Z K m))) := by
    have hp := CoupledLawTightness.with_initial μ ξ (Y K) hξ (hYm K) ρ.toMeasure
      (isTightMeasureSet_singleton (μ := ρ.toMeasure)) hInitial (hTight K)
    have ht := hp.map (VectorMildPathTightness.continuous_joint (d := Fin n) H hH0)
    have he : Measure.map (fun z : Physical (d := Fin n)×(Fin n → C(Parameter,ℝ)) =>
        VectorMildPathTightness.path (d := Fin n) H hH0 z.1 z.2) ''
          Set.range (fun m => (μ m).map (fun ω => (ξ m ω,Y K m ω)))=
        Set.range (fun m => (μ m).map (Z K m)) := by
      rw [←Set.range_comp']
      congr 1
      funext m
      exact Measure.map_map (VectorMildPathTightness.continuous_joint (d := Fin n) H hH0).measurable
        ((hξ m).prodMk (hYm K m))
    rwa [he] at ht
  let X : ∀ m,Ξ m → Path H (Physical (d := Fin n)) := fun m => NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hcU m)
  have hX (m : ℕ) : Measurable (X m) := NativeContinuousPath.measurable_path H
    (fun t ω => U m (t,ω)) (hcU m) ((hU m).mono (predictable_le_product (D m))).measurable
  let error := fun K => ⨆ m,(μ m) {ω | ContinuousNormExit.exit (fun t ω => U m (t,ω)) (K+1) ω≤(H : WithTop ℝ≥0)}
  have he : Filter.Tendsto error Filter.atTop (nhds 0) :=
    (MatrixUnboundedExitTail.uniform_nonexplosion G hG hβ hβ1 ell hell hLower H hH hH0 D μ U hU hcU
      radii B hnull ξ hξ hEq ρ hInitial).comp (Filter.tendsto_add_atTop_nat 1)
  apply TightnessByLocalization.tight μ X hX Z hZ htZ error he
  intro K m
  apply (show (μ m) {ω | X m ω≠Z K m ω}≤
    (μ m) {ω | ContinuousNormExit.exit (fun t ω => U m (t,ω)) (K+1) ω≤(H : WithTop ℝ≥0)} from ?_).trans
      (le_iSup (fun m => (μ m) {ω | ContinuousNormExit.exit (fun t ω => U m (t,ω)) (K+1) ω≤(H : WithTop ℝ≥0)}) m)
  apply measure_mono_ae
  have hs := MatrixLocalizedMildPath.state_before (D m) (G_R (radii m)) (U m) (hU m) (μ m) H hH hH0
    (hcU m) (K+1) (B m) (hnull m) (ξ m) (hξ m) (hEq m) (Y K m)
    (fun p i => hrep K i m p) (hzero K m)
  filter_upwards [hs] with ω hω hneq
  by_contra hτ
  have hHτ : (H : WithTop ℝ≥0)<ContinuousNormExit.exit (fun t ω => U m (t,ω)) (K+1) ω := lt_of_not_ge hτ
  apply hneq
  apply ContinuousMap.ext
  intro t
  have htH : toNN H t≤H := t.property.2
  have htτ : (toNN H t : WithTop ℝ≥0)≤ContinuousNormExit.exit (fun t ω => U m (t,ω)) (K+1) ω :=
    (WithTop.coe_le_coe.mpr htH).trans hHτ.le
  have hv := hω t htτ
  change U m (t.val.toNNReal,ω)=_
  have htime : t.val.toNNReal=toNN H t := by
    change t.val.toNNReal=⟨t.val,t.property.1⟩
    exact Real.toNNReal_of_nonneg t.property.1
  rw [htime]
  exact hv

end SHEStochastic.MatrixUnboundedPathTightness
