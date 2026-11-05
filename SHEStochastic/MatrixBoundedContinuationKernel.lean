module

public import SHEStochastic.MatrixFourierLimitKernel
public import SHEStochastic.MatrixFourierApproximationLimit
public import SHEStochastic.MatrixSmoothApproximationInputs
public import SHEStochastic.MatrixSmoothRandomSolutionFamily
public import SHEStochastic.MatrixConditionalMildMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixBoundedContinuationKernel
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open MatrixSmoothApproximation MatrixSmoothApproximationInputs
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
def holderCap (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) (C : ℝ≥0) : ℝ≥0 :=
  ⟨holderConstant G C,holderConstant_nonneg G C.coe_nonneg⟩

theorem target_holder (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) : HolderWith (holderCap G C) β (MatrixSmoothCoefficient.coefficient G 0).value := by
  have hnorm (z w : EuclideanSpace ℝ (Fin n)) : ‖G.value z-G.value w‖≤(C : ℝ)*‖z-w‖^(β : ℝ) := by
    simpa only [dist_eq_norm] using hG.dist_le z w
  exact holder_family G C.coe_nonneg β.coe_nonneg hnorm 0

abbrev Brownian (H : ℝ≥0) (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H)) :=
  ∀ m (j : Fin m → Fin n×HaarNode),FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration H)
    Q.toMeasure H (fun i => CanonicalStateDriverFiltration.coordinate H (j i))
      (fun i k => if j i=j k then 1 else 0)

def FourierSolution (H : ℝ≥0) (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1)
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H))
    (hBrown : Brownian H Q) : Prop :=
  MatrixFourierMildRealization.RandomEquation (CanonicalStateDriverFiltration.filtration H) Q.toMeasure H
    (MatrixSmoothCoefficient.coefficient G 0) (target_holder G hG) hβ hβ1
    (fun p => CanonicalStateDriverFiltration.state H p.1 p.2) (CanonicalStateDriverFiltration.state_predictable H)
    (MatrixCanonicalFourierRecognition.family H Q.toMeasure hBrown) (CanonicalStateDriverFiltration.state H 0)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (N : FiniteScalarIto.Family F μ H (Fin n×HaarNode))
    (ξ : Ω → Physical (d := Fin n)) (hξ₀ : StronglyMeasurable[F 0] ξ) (hξ : MemLp ξ 2 μ)

include hG hβ hβ1 hH0 hnull N hξ₀ hξ in
/-- One actual random-initial approximation limit supplies Borel
continuation laws at almost every reached initial state. The canonical
positive square factor has exactly the original covariance; no global
selection of a solution at every state is assumed. -/
theorem exists_kernel_with_fourier :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H),∃ hBrown : Brownian H Q,
      Q.toMeasure.map (CanonicalInitialLaw.initial H)=
        μ.map (fun ω => (ξ ω,fun _ : Fin n×HaarNode => (0 : ℝ))) ∧
      MatrixConditionalMildSolution.Supports H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH ∧
      FourierSolution H G hG hβ hβ1 Q hBrown := by
  have hGnorm (z w : EuclideanSpace ℝ (Fin n)) : ‖G.value z-G.value w‖ ≤ (C : ℝ)*‖z-w‖^(β : ℝ) := by
    simpa only [dist_eq_norm] using hG.dist_le z w
  have hβr : 0 < (β : ℝ) := by exact_mod_cast hβ
  let C0 : ℝ≥0 := ⟨holderConstant G C,holderConstant_nonneg G C.coe_nonneg⟩
  have hh (ε : ℝ) : HolderWith C0 β (MatrixSmoothCoefficient.coefficient G ε).value :=
    holder_family G C.coe_nonneg β.coe_nonneg hGnorm ε
  obtain ⟨U,hU,hc,hEq,_⟩ := MatrixSmoothRandomSolutionFamily.exists_family G C.coe_nonneg hβr hGnorm
    hH hH0 hnull N ξ hξ₀ hξ
  obtain ⟨noise,hnoise,Q,φ,hφ,hlim,hBrown,hInitial,_⟩ := MatrixFourierApproximationLimit.exists_random_limit
    F μ H hH hH0 (coefficient G) (fun _ => N) U hU hc
    (fun m => hh (CompactMollifier.radius m)) hβ hβ1 G.bound (fun _ => le_rfl)
    ξ ((hξ₀.mono (F.le 0)).measurable) hnull
    (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G) (fun _ => le_rfl) hEq
  refine ⟨Q,hBrown,hInitial,?_,?_⟩
  · exact MatrixFourierLimitKernel.supports F μ H (coefficient G)
      (fun m => hh (CompactMollifier.radius m)) hβ hβ1 noise U hU hc ξ hnoise
      (MatrixSmoothCoefficient.coefficient G 0) (hh 0) G.bound (fun _ => le_rfl)
      (error G C β) (error_nonneg G C.coe_nonneg β) (error_tendsto G C hβr)
      (close G C.coe_nonneg hβr hGnorm) Q φ hφ hlim hH hnull hBrown
  · exact MatrixFourierLimitKernel.fourier F μ H (coefficient G)
      (fun m => hh (CompactMollifier.radius m)) hβ hβ1 noise U hU hc ξ hnoise
      (MatrixSmoothCoefficient.coefficient G 0) (hh 0) G.bound (fun _ => le_rfl)
      (error G C β) (error_nonneg G C.coe_nonneg β) (error_tendsto G C hβr)
      (close G C.coe_nonneg hβr hGnorm) Q φ hφ hlim hnull hBrown

include hG hβ hβ1 hH0 hnull N hξ₀ hξ in
theorem exists_kernel :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H),
      Q.toMeasure.map (CanonicalInitialLaw.initial H)=
        μ.map (fun ω => (ξ ω,fun _ : Fin n×HaarNode => (0 : ℝ))) ∧
      MatrixConditionalMildSolution.Supports H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH := by
  obtain ⟨Q,hBrown,hInitial,hSupport,_⟩ := exists_kernel_with_fourier F μ H G hG hβ hβ1 hH hH0 hnull N ξ hξ₀ hξ
  exact ⟨Q,hInitial,hSupport⟩

include hG hβ hβ1 hH0 N in
/-- A Borel continuation kernel for any prescribed square-integrable
initial law. It is needed only at that law's almost-everywhere reached
states; no selection over all initial states is postulated. -/
theorem exists_kernel_from_law
    (ρ : ProbabilityMeasure (Physical (d := Fin n)))
    (hρ : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2 ρ.toMeasure) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H),
      CanonicalInitialKernel.initialLaw H Q.toMeasure=ρ.toMeasure ∧
      MatrixConditionalMildSolution.Supports H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH := by
  let D := RandomInitialBrownianFamily.filtration ρ.toMeasure μ F
  let ν := IndependentNoiseCompletion.measure ρ.toMeasure μ
  let Z : RandomInitialBrownianFamily.Space ρ.toMeasure μ → Physical (d := Fin n) := Prod.fst
  have hmZ : Measurable Z := (IndependentNoiseCompletion.fst_preserving ρ.toMeasure μ).measurable
  have haZ : StronglyMeasurable[D 0] Z :=
    (RandomInitialBrownianFamily.initial_adapted ρ.toMeasure μ F 0).stronglyMeasurable
  have hZ : MemLp Z 2 ν :=
    hρ.comp_measurePreserving (IndependentNoiseCompletion.fst_preserving ρ.toMeasure μ)
  obtain ⟨Q,hInitial,hSupport⟩ := exists_kernel D ν H G hG hβ hβ1 hH hH0
    (RandomInitialBrownianFamily.contains_null ρ.toMeasure μ F)
    (RandomInitialBrownianFamily.family ρ.toMeasure μ F H N) Z haZ hZ
  exact ⟨Q,(CanonicalInitialKernel.initialLaw_eq_of_joint H Q.toMeasure ν Z hmZ hInitial).trans
    (IndependentNoiseCompletion.fst_preserving ρ.toMeasure μ).map_eq,hSupport⟩

include hG hβ hβ1 hH0 N in
/-- The very same continuation law retains its unconditional Fourier
equation and its original canonical Brownian family. -/
theorem exists_kernel_from_law_with_fourier
    (ρ : ProbabilityMeasure (Physical (d := Fin n)))
    (hρ : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2 ρ.toMeasure) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H),∃ hBrown : Brownian H Q,
      CanonicalInitialKernel.initialLaw H Q.toMeasure=ρ.toMeasure ∧
      MatrixConditionalMildSolution.Supports H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH ∧
      FourierSolution H G hG hβ hβ1 Q hBrown := by
  let D := RandomInitialBrownianFamily.filtration ρ.toMeasure μ F
  let ν := IndependentNoiseCompletion.measure ρ.toMeasure μ
  let Z : RandomInitialBrownianFamily.Space ρ.toMeasure μ → Physical (d := Fin n) := Prod.fst
  have hmZ : Measurable Z := (IndependentNoiseCompletion.fst_preserving ρ.toMeasure μ).measurable
  have haZ : StronglyMeasurable[D 0] Z :=
    (RandomInitialBrownianFamily.initial_adapted ρ.toMeasure μ F 0).stronglyMeasurable
  have hZ : MemLp Z 2 ν := hρ.comp_measurePreserving (IndependentNoiseCompletion.fst_preserving ρ.toMeasure μ)
  obtain ⟨Q,hBrown,hInitial,hSupport,hFourier⟩ := exists_kernel_with_fourier D ν H G hG hβ hβ1 hH hH0
    (RandomInitialBrownianFamily.contains_null ρ.toMeasure μ F)
    (RandomInitialBrownianFamily.family ρ.toMeasure μ F H N) Z haZ hZ
  exact ⟨Q,hBrown,(CanonicalInitialKernel.initialLaw_eq_of_joint H Q.toMeasure ν Z hmZ hInitial).trans
    (IndependentNoiseCompletion.fst_preserving ρ.toMeasure μ).map_eq,hSupport,hFourier⟩

include hG hβ hβ1 hH0 N in
theorem exists_restartable_with_fourier
    (ρ : ProbabilityMeasure (Physical (d := Fin n)))
    (hρ : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2 ρ.toMeasure) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H),∃ hBrown : Brownian H Q,
      CanonicalInitialKernel.initialLaw H Q.toMeasure=ρ.toMeasure ∧
      MatrixConditionalMildSolution.Supports H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH ∧
      FourierSolution H G hG hβ hβ1 Q hBrown ∧
      ∀ t : ℝ≥0,t≤H → MemLp (CanonicalStateDriverFiltration.state H t) 2 Q.toMeasure := by
  obtain ⟨Q,hBrown,hLaw,hSupport,hFourier⟩ := exists_kernel_from_law_with_fourier F μ H G hG hβ hβ1 hH hH0 N ρ hρ
  have hInitial : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2
      (CanonicalInitialKernel.initialLaw H Q.toMeasure) := by rw [hLaw];exact hρ
  exact ⟨Q,hBrown,hLaw,hSupport,hFourier,fun t ht => MatrixConditionalMildMoments.mixture_state_memLp
    H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH hSupport hInitial t ht⟩

include hG hβ hβ1 hH0 N in
/-- The local continuation can be repeated from every reached L2 law.
Both the solution kernel and the moment needed for the next join are
constructed from the given initial law. -/
theorem exists_restartable_kernel
    (ρ : ProbabilityMeasure (Physical (d := Fin n)))
    (hρ : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2 ρ.toMeasure) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space
      (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H),
      CanonicalInitialKernel.initialLaw H Q.toMeasure=ρ.toMeasure ∧
      MatrixConditionalMildSolution.Supports H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH ∧
      ∀ t : ℝ≥0,t≤H → MemLp (CanonicalStateDriverFiltration.state H t) 2 Q.toMeasure := by
  obtain ⟨Q,hLaw,hSupport⟩ := exists_kernel_from_law F μ H G hG hβ hβ1 hH hH0 N ρ hρ
  have hInitial : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2
      (CanonicalInitialKernel.initialLaw H Q.toMeasure) := by rw [hLaw]; exact hρ
  exact ⟨Q,hLaw,hSupport,fun t ht => MatrixConditionalMildMoments.mixture_state_memLp
    H Q.toMeasure (MatrixSmoothCoefficient.coefficient G 0) hH hSupport hInitial t ht⟩

end SHEStochastic.MatrixBoundedContinuationKernel
