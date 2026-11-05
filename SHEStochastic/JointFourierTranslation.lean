module

public import SHEStochastic.JointFourierProblem

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.JointFourierTranslation
open MeasureTheory ProbabilityTheory SHE SHE.DyadicApproximation GaussianItoTest
open FiniteStateDriverCoordinates JointFourierCylinderGenerator StoppedPathPasting
open SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι]

def shift (v : ι → ℝ) : C(RealL2 × (ι → ℝ), RealL2 × (ι → ℝ)) :=
  ⟨fun q ↦ (q.1, fun i ↦ v i+q.2 i), continuous_fst.prodMk
    (continuous_pi fun i ↦ continuous_const.add ((continuous_apply i).comp continuous_snd))⟩

variable {s d : ℕ} (driver : Fin d → ι) (v : ι → ℝ)

def offset : State (s+d) := append (0 : State s) (WithLp.toLp 2 (fun j ↦ v (driver j)))

def translated (f : State (s+d) → ℝ) : State (s+d) → ℝ :=
  fun z ↦ f (offset (s := s) driver v+z)

theorem contDiff_translated {k : WithTop ℕ∞} {f : State (s+d) → ℝ} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (translated driver v f) :=
  hf.comp (contDiff_const.add contDiff_id)

theorem support_translated {f : State (s+d) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (translated driver v f) :=
  hf.comp_homeomorph (Homeomorph.addLeft (offset (s := s) driver v))

theorem projection_shift (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
    (q : RealL2 × (ι → ℝ)) :
    projection a n driver (shift v q) = offset driver v+projection a n driver q := by
  apply PiLp.ext
  refine Fin.addCases ?_ ?_
  · intro i
    simp [offset, projection_left, shift]
  · intro j
    simp [offset, projection_right, shift]

theorem hessian_translated (f : State (s+d) → ℝ) (z : State (s+d)) :
    GaussianTaylor.hessian (translated driver v f) z =
      GaussianTaylor.hessian f (offset driver v+z) := by
  have hd : fderiv ℝ (translated driver v f) =
      fun x ↦ fderiv ℝ f (offset driver v+x) := by
    funext x
    exact fderiv_comp_add_left _
  rw [GaussianTaylor.hessian, hd, fderiv_comp_add_left]
  rfl

theorem heatDrift_translated (n : Fin s → ℤ) (f : State (s+d) → ℝ)
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) (z : State (s+d)) :
    FourierCylinderGenerator.heatDrift (translated driver v f) (contDiff_translated driver v hf)
      (support_translated driver v hs) (frequencies (d := d) n) z =
    FourierCylinderGenerator.heatDrift f hf hs (frequencies (d := d) n) (offset driver v+z) := by
  rw [FourierCylinderGenerator.heatDrift_apply, FourierCylinderGenerator.heatDrift_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hw : -(frequencies (d := d) n i : ℝ)^2*(offset (s := s) driver v+z) i =
      -(frequencies (d := d) n i : ℝ)^2*z i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [frequencies, offset]
    · intro j
      simp [frequencies]
  rw [hw]
  congr 1
  exact congrArg (fun A : State (s+d) →L[ℝ] ℝ ↦
    A (EuclideanSpace.basisFun (Fin (s+d)) ℝ i)) (fderiv_comp_add_left _)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β ≤ 1)
  (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z, ‖G z‖ ≤ B)
  (a : Fin s → ℂ →L[ℝ] ℝ) (n : Fin s → ℤ)
  (b : Fin d → Lp V 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)))
  (f : State (s+d) → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)

theorem test_translated :
    test a n driver (translated driver v f) (contDiff_translated driver v hf)
      (support_translated driver v hs) = (test a n driver f hf hs).compContinuous (shift v) := by
  ext q
  change f (offset driver v+projection a n driver q) = f (projection a n driver (shift v q))
  rw [projection_shift]

theorem generator_translated :
    generator hG hβ hβ1 B hB hb a n b driver (translated driver v f)
      (contDiff_translated driver v hf) (support_translated driver v hs) =
      (generator hG hβ hβ1 B hB hb a n b driver f hf hs).compContinuous (shift v) := by
  ext q
  change generator hG hβ hβ1 B hB hb a n b driver (translated driver v f)
      (contDiff_translated driver v hf) (support_translated driver v hs) q =
    generator hG hβ hβ1 B hB hb a n b driver f hf hs (shift v q)
  rw [generator_apply, generator_apply, projection_shift, heatDrift_translated]
  simp only [hessian_translated]
  rfl

/-- Driver translation preserves every joint cylinder identity, because
the driver has zero heat drift and all covariance rows depend only on
the state. No additional stochastic theorem is used. -/
theorem problem (H : ℝ≥0) (e : HilbertBasis ι ℝ (Lp V 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))))
    (μ : Measure (Path H (RealL2 × (ι → ℝ))))
    (h : JointFourierProblem.Holds hG hβ hβ1 B hB hb H e μ) :
    JointFourierProblem.Holds hG hβ hβ1 B hB hb H e
      (μ.map (fun x ↦ (shift v).comp x)) := by
  intro s d a n driver f hf hSmooth hs
  apply PastedCylinderMartingale.Identity.map_state H (shift v)
  rw [← test_translated driver v a n f hf hs,
    ← generator_translated driver v hG hβ hβ1 B hB hb a n (fun j ↦ e (driver j)) f hf hs]
  exact h a n driver (translated driver v f) (contDiff_translated driver v hf)
    (contDiff_translated driver v hSmooth) (support_translated driver v hs)

theorem continuation_problem (H : ℝ≥0)
    (e : HilbertBasis ι ℝ (Lp V 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))))
    (κ : Kernel RealL2 (SHE.CanonicalContinuousStateDriver.Space (E := RealL2) (ι := ι) H))
    [IsMarkovKernel κ] (z : RealL2 × (ι → ℝ))
    (h : JointFourierProblem.Holds hG hβ hβ1 B hB hb H e
      ((κ z.1).map (JointStateDriverPath.pack H))) :
    JointFourierProblem.Holds hG hβ hβ1 B hB hb H e
      (JointStateDriverPath.continuationKernel H κ z) := by
  intro s d a n driver f hf hSmooth hs
  have hm : Measurable (fun x : Path H (RealL2 × (ι → ℝ)) ↦ (shift z.2).comp x) :=
    ContinuousMap.measurable_iff_eval.mpr fun t ↦
      (shift z.2).continuous.measurable.comp (ContinuousMap.measurable_eval t)
  have he : JointStateDriverPath.continuationKernel H κ z =
      ((κ z.1).map (JointStateDriverPath.pack H)).map (fun x ↦ (shift z.2).comp x) := by
    rw [JointStateDriverPath.continuationKernel_apply,
      Measure.map_map hm (JointStateDriverPath.measurable_pack H)]
    rfl
  rw [he]
  exact problem z.2 hG hβ hβ1 B hB hb H e _ h a n driver f hf hSmooth hs

end SHEStochastic.JointFourierTranslation
