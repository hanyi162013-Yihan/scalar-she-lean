module

public import SHEStochastic.UnboundedExitInitialLaw
public import SHEStochastic.UnboundedFourierStoppedMartingale
public import SHEStochastic.BoundedLocalMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativeUniformStoppedFourier
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle Filter
open UnboundedNativeHeatEquation UnboundedNativeUniformRegularity StoppedPathPasting
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology

variable {Ω V ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (P : FiniteScalarIto.Family F μ H ι)
  (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (u₀ : RealL2)
  (hH : 0 < H) (hcW : ∀ ω, Continuous (fun t ↦ W t ω))
  (hnull : NullCompleteFiltration.ContainsNullSets F μ)
  (hEquation : Equation F μ H W hW hG hβ hβ1 P e u₀)
  (M : ℝ) (hM : 0 ≤ M)
  (hu₀ : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀ = ENNReal.ofReal M)

include hH hnull hEquation hM hu₀ in
theorem state_bound (R : ℕ) (hR : M ≤ R) :
    ∀ᵐ ω ∂μ, ∀ t : Time (min H 1), t ≤ uniformExit H W hcW R ω →
      ‖NativeContinuousPath.path (min H 1) W hcW ω t‖ ≤ R := by
  filter_upwards [regularity F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀,
    real_norm_initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀]
    with ω hreg hzero t ht
  have hb := UniformCoefficientExit.before_or_at_bound (haarAddCircle (T := 1)) (min H 1) R
    (NativeContinuousPath.path (min H 1) W hcW ω) hreg.1 hreg.2 (hzero.trans_le hR) t ht
  have ha := (L2ExtendedUniformNorm.le_ofReal_iff (haarAddCircle (T := 1))
    (NativeContinuousPath.path (min H 1) W hcW ω t) R (by positivity)).mp hb
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity : (0 : ℝ) ≤ R) ha

def coordinate (a : ℂ →L[ℝ] ℝ) (n : ℤ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((q : ℝ)*(n : ℝ)^2)*NativeFourierHeatCoordinate.coordinate a n (W q ω)-
    NativeFourierHeatCoordinate.coordinate a n (W 0 ω)

include hW in
/-- Remove L2 localization using the uniform bound of the stopped
source. Both horizon versions reuse this domination argument. -/
theorem martingale_of_stopped (K : ℝ≥0) (r : Ω → Time K)
    (R : ℕ) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (hτ : IsStoppingTime F (fun ω ↦ (AdaptedCanonicalPathTests.toNN K (r ω) : WithTop ℝ≥0)))
    (hInitial : W 0 =ᵐ[μ] fun _ ↦ u₀)
    (hSource : ∀ N : ℕ, Martingale
      (stoppedProcess (UnboundedFourierStoppedMartingale.fluctuation W u₀ a n)
        (fun ω ↦ min (K : WithTop ℝ≥0) (exit W N ω))) F μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ t : Time K, t ≤ r ω →
      ‖NativeContinuousPath.path K W hcW ω t‖ ≤ R) :
    Martingale (stoppedProcess (coordinate W a n)
      (fun ω ↦ (AdaptedCanonicalPathTests.toNN K (r ω) : WithTop ℝ≥0))) F μ := by
  let τ : Ω → WithTop ℝ≥0 := fun ω ↦ AdaptedCanonicalPathTests.toNN K (r ω)
  let Z := coordinate W a n
  let O := UnboundedFourierStoppedMartingale.fluctuation W u₀ a n
  have hτK (ω : Ω) : τ ω ≤ (K : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr (r ω).property.2
  have haZ : StronglyAdapted F Z := by
    intro q
    have hw := (show IsStronglyPredictable F W from hW).stronglyAdapted
    exact (stronglyMeasurable_const.mul
      ((NativeFourierHeatCoordinate.coordinate a n).continuous.comp_stronglyMeasurable (hw q))).sub
        ((NativeFourierHeatCoordinate.coordinate a n).continuous.comp_stronglyMeasurable
          ((hw 0).mono (F.mono bot_le)))
  have hcZ (ω : Ω) : Continuous (fun q ↦ Z q ω) := by
    unfold Z coordinate
    fun_prop
  have hcO (ω : Ω) : Continuous (fun q ↦ O q ω) := by
    unfold O UnboundedFourierStoppedMartingale.fluctuation
    fun_prop
  have ha := haZ.stoppedProcess hcZ hτ
  have hc (ω : Ω) := (hcZ ω).stoppedProcess τ

  have he : ∀ᵐ ω ∂μ, ∀ q, Z q ω = O q ω := by
    filter_upwards [hInitial] with ω hω q
    simp only [Z, coordinate, O, UnboundedFourierStoppedMartingale.fluctuation, hω]
  have hSeq : IsLocalizingSequence F (fun N ↦ exit W N) μ :=
    { isStoppingTime := exit_stopping F W hW hcW
      mono := Eventually.of_forall (ContinuousNormExit.monotone (fun t ω ↦ physical W (t,ω)) (physical_continuous W hcW))
      tendsto_top := Eventually.of_forall (ContinuousNormExit.tendsto_top (fun t ω ↦ physical W (t,ω)) (physical_continuous W hcW)) }
  have hStopped (N : ℕ) : Martingale (stoppedProcess (stoppedProcess Z τ) (exit W N)) F μ := by
    have hm := (hSource N).stoppedProcess
      (fun ω q ↦ ((hcO ω).stoppedProcess
        (fun ω ↦ min (K : WithTop ℝ≥0) (exit W N ω))).continuousAt.continuousWithinAt) hτ
    have hcomm : stoppedProcess (stoppedProcess O (fun ω ↦ min (K : WithTop ℝ≥0) (exit W N ω))) τ =
        stoppedProcess (stoppedProcess O τ) (exit W N) := by
      simp only [stoppedProcess_stoppedProcess']
      congr 1
      funext ω
      change min (τ ω) (min (K : WithTop ℝ≥0) (exit W N ω)) = min (exit W N ω) (τ ω)
      rw [← min_assoc, min_eq_left (hτK ω), min_comm]
    rw [hcomm] at hm
    have hh := stoppedProcess_congr (τ := exit W N) (stoppedProcess_congr (τ := τ) he)
    exact hm.congr (ha.stoppedProcess hc (hSeq.isStoppingTime N))
      (fun q ↦ hh.mono fun ω hω ↦ (hω q).symm)
  have hzero (ω : Ω) : stoppedProcess Z τ 0 ω = 0 := by
    rw [stoppedProcess_eq_of_le (show (0 : WithTop ℝ≥0) ≤ τ ω from bot_le)]
    simp [Z, coordinate]
  have hl := BoundedLocalMartingale.locally_of_stopped μ F _ hzero _ hSeq hStopped
  apply BoundedLocalMartingale.martingale_of_dominated μ F _ ha hl
    (fun _ ↦ Real.exp ((K : ℝ)*(n : ℝ)^2)*‖NativeFourierHeatCoordinate.coordinate a n‖*R+
      ‖NativeFourierHeatCoordinate.coordinate a n‖*R) (integrable_const _)
  filter_upwards [hBound]
    with ω hbound q
  let t := pastTime K (r ω) (AdaptedCanonicalPathTests.clock K q)
  have ht : t ≤ r ω := min_le_right _ _
  have h0 : origin K ≤ r ω := (r ω).property.1
  have hread : ((min (q : WithTop ℝ≥0) (τ ω)).untopA : ℝ) = t.val := by
    change (((min (q : WithTop ℝ≥0)
      (AdaptedCanonicalPathTests.toNN K (r ω) : WithTop ℝ≥0)).untopA : ℝ)) =
        min (min (q : ℝ) (K : ℝ)) (r ω).val
    rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    simp only [NNReal.coe_min, AdaptedCanonicalPathTests.toNN]
    rw [min_assoc, min_eq_right (r ω).property.2]
    exact NNReal.coe_min _ _
  have hNN : (min (q : WithTop ℝ≥0) (τ ω)).untopA = t.val.toNNReal := by
    apply NNReal.eq
    rw [hread, Real.coe_toNNReal _ t.property.1]
  have htW : ‖W (min (q : WithTop ℝ≥0) (τ ω)).untopA ω‖ ≤ R := by
    rw [hNN]
    exact hbound t ht
  have hzeroW : ‖W 0 ω‖ ≤ R := by
    simpa only [NativeContinuousPath.path, ContinuousMap.coe_mk, origin, Real.toNNReal_zero] using
      hbound (origin K) h0
  change ‖Real.exp _*NativeFourierHeatCoordinate.coordinate a n (W _ ω)-
    NativeFourierHeatCoordinate.coordinate a n (W 0 ω)‖ ≤ _
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply add_le_add
  · have he : Real.exp (((min (q : WithTop ℝ≥0) (τ ω)).untopA : ℝ)*(n : ℝ)^2) ≤
        Real.exp ((K : ℝ)*(n : ℝ)^2) := by
      rw [hread]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right t.property.2 (sq_nonneg _))
    simpa only [mul_assoc] using mul_le_mul he
      ((NativeFourierHeatCoordinate.coordinate a n).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left htW (norm_nonneg _))) (norm_nonneg _) (Real.exp_pos _).le
  · exact (NativeFourierHeatCoordinate.coordinate a n).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_left hzeroW (norm_nonneg _))


include hH hnull hEquation hM hu₀ in
/-- The actual Fourier fluctuation stopped at its uniform exit is a
genuine martingale. The L2 localization is removed by the derived
almost-sure deterministic bound, not by a new integrability hypothesis. -/
theorem martingale (R : ℕ) (hR : M ≤ R) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    Martingale (stoppedProcess (coordinate W a n)
      (fun ω ↦ (AdaptedCanonicalPathTests.toNN (min H 1) (uniformExit H W hcW R ω) : WithTop ℝ≥0))) F μ := by
  exact martingale_of_stopped F μ W hW u₀ hcW (min H 1) (uniformExit H W hcW R) R a n
    (UnboundedNativeUniformRegularity.isStoppingTime F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation M hM hu₀ R)
    (UnboundedNativeMildRecognition.initial F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation)
    (fun N ↦ UnboundedFourierStoppedMartingale.martingale F μ H W hW hG hβ hβ1 P e u₀
      hH hcW hnull hEquation N a n)
    (state_bound F μ H W hW hG hβ hβ1 P e u₀ hH hcW hnull hEquation M hM hu₀ R hR)

end SHEStochastic.NativeUniformStoppedFourier
