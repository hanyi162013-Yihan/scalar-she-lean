module

public import SHEStochastic.VectorHeatObservation
public import SHE.UniformSmooth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.VectorPhysicalRootTest
open MeasureTheory SHE SHE.StoppedFourier SHE.GaussianIncrement SHE.UniformSmooth MatrixInfiniteHaar
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩


/-- Positive-age observations are jointly Borel in their center and L2 input. -/
theorem observation_measurable {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun p : HeatCircle×Physical (d := Fin n) => VectorHeatObservation.observation ε p.1 p.2) := by
  have hm : Measurable (fun p : HeatCircle×Physical (d := Fin n) => VectorHeatMean.mean p.2 (ε,p.1)) :=
    Measurable.comp
      (g := fun p : Physical (d := Fin n)×(ℝ×HeatCircle) => VectorHeatMean.mean p.1 p.2)
      (f := fun p : HeatCircle×Physical (d := Fin n) => (p.2,(ε,p.1)))
      VectorHeatMean.measurable (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))
  simpa only [VectorHeatObservation.mean hε] using hm


def value (age : Fin k → ℝ) (center : Fin k → HeatCircle) (color : Fin k → Fin n)
    (w : Fin k → ℝ) (U V : Ω → Physical (d := Fin n)) (r : HeatCircle×Ω) : State k :=
  WithLp.toLp 2 (fun i => VectorHeatObservation.observation (age i) (center i+r.1)
    (U r.2+w i • (V r.2-U r.2)) (color i))

theorem measurable (age : Fin k → ℝ) (hAge : ∀ i,0 < age i)
    (center : Fin k → HeatCircle) (color : Fin k → Fin n) (w : Fin k → ℝ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) :
    Measurable (value age center color w U V) := by
  apply ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.continuous.measurable).comp
  apply measurable_pi_iff.mpr
  intro i
  have hState : Measurable (fun r : HeatCircle×Ω => U r.2+w i • (V r.2-U r.2)) :=
    (hU.comp measurable_snd).add (((hV.comp measurable_snd).sub (hU.comp measurable_snd)).const_smul (w i))
  have hCenter : Measurable (fun r : HeatCircle×Ω => center i+r.1) := measurable_const.add measurable_fst
  have hObs : Measurable (fun r : HeatCircle×Ω =>
      VectorHeatObservation.observation (age i) (center i+r.1) (U r.2+w i • (V r.2-U r.2))) :=
    Measurable.comp
      (g := fun p : HeatCircle×Physical (d := Fin n) => VectorHeatObservation.observation (age i) p.1 p.2)
      (f := fun r : HeatCircle×Ω => (center i+r.1,U r.2+w i • (V r.2-U r.2)))
      (observation_measurable (hAge i)) (hCenter.prodMk hState)
  exact (EuclideanSpace.proj (𝕜 := ℝ) (color i)).continuous.measurable.comp hObs


/-- The literal regularized mixed-root observable is jointly integrable;
all spatial and probability Fubini steps use this bound. -/
theorem integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (age : Fin k → ℝ) (hAge : ∀ i,0 < age i)
    (center : Fin k → HeatCircle) (color : Fin k → Fin n) (w : Fin k → ℝ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V)
    (F : HeatCircle → State k → ℝ) (hF : UniformBoundedSmooth F)
    (hFm : Measurable (fun p : HeatCircle×State k => F p.1 p.2)) :
    Integrable (fun r : HeatCircle×Ω => F r.1 (value age center color w U V r))
      (AddCircle.haarAddCircle.prod μ) := by
  obtain ⟨M,hM,hBound⟩ := hF.norm_bound
  exact Integrable.of_bound
    (hFm.comp (measurable_fst.prodMk (measurable age hAge center color w U V hU hV))).aestronglyMeasurable
    M (ae_of_all _ (fun r => hBound r.1 _))

end SHEStochastic.VectorPhysicalRootTest
