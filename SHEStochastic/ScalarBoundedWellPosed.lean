module

public import SHEStochastic.GlobalScalarVarianceNormalization
public import SHEStochastic.GlobalCanonicalFourierMildSolution
public import SHEStochastic.GlobalBoundedComparisonProof
public import SHEStochastic.CanonicalBrownianFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarBoundedWellPosed
open MeasureTheory ProbabilityTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier
  CanonicalStateDriverFiltration StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace ScalarVarianceNormalization.Noise := borel _
local instance : BorelSpace ScalarVarianceNormalization.Noise := ⟨rfl⟩

/-- Lower the bounded diffusion's positive Hölder exponent into the
open unit interval used by the original native scalar theorem. -/
theorem effective_exponent {g : ℝ→ℝ} {C β₀ : ℝ≥0} (hg : HolderWith C β₀ g) (hβ₀ : 0<β₀)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B) :
    ∃ C' β : ℝ≥0,0<β ∧ β<1 ∧ HolderWith C' β g := by
  let β := min β₀ (1/2 : ℝ≥0)
  have hp : 0<β := lt_min hβ₀ (by norm_num)
  have ht : β<1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨max C (2*B),β,hp,ht,?_⟩
  have hd (x y : ℝ) : dist (g x) (g y) ≤ ((max C (2*B) : ℝ≥0) : ℝ)*dist x y^(β : ℝ) := by
    by_cases hxy : x = y
    · subst y
      rw [dist_self,dist_self]
      positivity
    by_cases h : dist x y ≤ 1
    · have he : (β : ℝ)≤(β₀ : ℝ) := min_le_left _ _
      have hPow := Real.rpow_le_rpow_of_exponent_ge (dist_pos.mpr hxy) h he
      calc
        _ ≤ (C : ℝ)*dist x y^(β₀ : ℝ) := hg.dist_le x y
        _ ≤ (C : ℝ)*dist x y^(β : ℝ) := mul_le_mul_of_nonneg_left hPow C.coe_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    · have hPow : 1≤dist x y^(β : ℝ) := Real.one_le_rpow (le_of_lt (lt_of_not_ge h)) β.coe_nonneg
      calc
        _ ≤ ‖g x‖+‖g y‖ := dist_le_norm_add_norm _ _
        _ ≤ (2*B : ℝ) := by linarith [hb x,hb y]
        _ ≤ ((max C (2*B) : ℝ≥0) : ℝ) := by exact_mod_cast (le_max_right C (2*B))
        _ ≤ _ := le_mul_of_one_le_right (NNReal.coe_nonneg _) hPow
  exact PositiveScalarApproximation.holder_of_bound (fun x y => by simpa only [Real.dist_eq] using hd x y)

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- Build the original scalar mild equation with its actual Brownian
driver from a deterministic L² initial profile, at any positive horizon. -/
theorem exists_canonical (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ1 : β<1)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B)
    (ell : ℝ) (hell : 0<ell) (he : ∀ z,ell≤(g z)^2)
    (e : HilbertBasis ι ℝ ScalarVarianceNormalization.Noise) (u₀ : RealL2) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H),
      ∃ P : FiniteScalarIto.Family (filtration (E := RealL2) (ι := ι) H) Q.toMeasure H ι,
        state H 0 =ᵐ[Q.toMeasure] (fun _ => u₀) ∧
        GlobalBoundedFourierRecognition.HasClosedVersion (filtration H) Q.toMeasure H (state H)
          (state_predictable H) hg hβ hβ1 B hb hH
          (FiniteCylindricalIto.terminalIto P.toCoordinates e) (state H 0) := by
  let : Encodable ι := Encodable.ofCountable ι
  let : SecondCountableTopology ScalarVarianceNormalization.Noise := e.repr.toHomeomorph.secondCountableTopology
  let source := CanonicalBrownianFamily.reindex (⟨Encodable.encode,Encodable.encode_injective⟩ : ι ↪ ℕ)
  let F := PredictableTimeDilation.filtration CanonicalBrownianFamily.filtration
    (PredictableTimeDilation.clock H hH)
  obtain ⟨P₀,_⟩ := NativeTimeDilatedFamily.exists_family CanonicalBrownianFamily.filtration
    CanonicalBrownianFamily.measure H hH 1 source e CanonicalBrownianFamily.contains_null
  have hP : Nonempty (FiniteScalarIto.Family F CanonicalBrownianFamily.measure H ι) :=
    ⟨by simpa only [mul_one] using P₀⟩
  have hρ : MemLp (id : RealL2→RealL2) 2 (Measure.dirac u₀) := by
    have heq : (id : RealL2→RealL2) =ᵐ[Measure.dirac u₀] fun _ => u₀ := by
      simp only [Filter.EventuallyEq,ae_dirac_eq,Filter.eventually_pure,id_eq]
    exact (memLp_congr_ae heq).mpr (memLp_const _)
  obtain ⟨Q,hInit,hBrown,hChar⟩ := GlobalScalarVarianceNormalization.exists_kernel hg hβ F
    CanonicalBrownianFamily.measure H hP.some e hβ1 B hb ell hell he hH (Measure.dirac u₀) hρ
  have hI := CanonicalInitialKernel.matching_initial H Q.toMeasure
  unfold NativeContinuationCharacteristics.BrownianInput at hBrown
  simp only [hInit,ae_dirac_eq,Filter.eventually_pure] at hBrown hChar hI
  have hChar₀ := hChar.1
  let ν : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H) :=
    ⟨CanonicalInitialKernel.kernel H Q.toMeasure u₀,inferInstance⟩
  let P := CanonicalNativeFourierRecognition.family H ν.toMeasure hBrown
  refine ⟨ν,P,hI,?_⟩
  apply GlobalCanonicalFourierMildSolution.exists_closed H ν.toMeasure hg hβ hβ1 B hb e hBrown hH
  intro a k
  obtain ⟨hM,hS,hC,hSG⟩ := hChar₀ a k
  exact CanonicalNativeFourierRecognition.equation H ν.toMeasure hg hβ hβ1 B hb e hBrown a k
    hM (fun t _ => (hSG t).memLp (2 : ℝ≥0)) hS hC

end SHEStochastic.ScalarBoundedWellPosed
