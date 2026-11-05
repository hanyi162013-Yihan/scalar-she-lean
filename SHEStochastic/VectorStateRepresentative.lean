module

public import SHEStochastic.VectorHeatMean
public import SHEStochastic.MatrixNemytskii
public import SHE.HeatPhysicalSubsequence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.VectorStateRepresentative
open MeasureTheory Set Filter SHE SHE.StoppedFourier SHE.DyadicApproximation
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {P : Type*} {n : ℕ}
local instance : SecondCountableTopology (VectorHeat.Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (VectorHeat.Physical (d := Fin n)) := borel _
local instance : BorelSpace (VectorHeat.Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

def component (U : P → VectorHeat.Physical (d := Fin n)) (i : Fin n) (p : P) : RealL2 :=
  VectorHeat.coordinates (U p) i

def unit (U : P → VectorHeat.Physical (d := Fin n)) (p : P × AddCircle (1 : ℝ)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => PredictableScalarField.unitField (component U i) p)

def native (U : P → VectorHeat.Physical (d := Fin n)) (p : P × HeatCircle) : EuclideanSpace ℝ (Fin n) :=
  unit U (p.1,CircleNormalization.scale (2*Real.pi) 1 p.2)

theorem unit_ae (U : P → VectorHeat.Physical (d := Fin n)) (p : P) :
    (fun x => unit U (p,x)) =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] U p := by
  filter_upwards [ae_all_iff.mpr (fun i => PredictableScalarField.unitField_ae (component U i) p),
    L2EuclideanCoordinates.coordinates_ae (AddCircle.haarAddCircle (T := (1 : ℝ))) (U p)] with x hx hc
  ext i
  exact (hx i).trans (hc i)

section Measurable
variable [MeasurableSpace P] (U : P → VectorHeat.Physical (d := Fin n)) (hU : Measurable U)
include hU

theorem component_measurable (i : Fin n) : Measurable (component U i) :=
  (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => RealL2) i).continuous.comp
    (VectorHeat.coordinates (d := Fin n)).continuous).measurable).comp hU

theorem unit_measurable : Measurable (unit U) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact measurable_pi_iff.mpr (fun i => PredictableScalarField.unitField_measurable (component_measurable U hU i))

theorem native_measurable : Measurable (native U) :=
  (unit_measurable U hU).comp (measurable_fst.prodMk
    ((CircleNormalization.continuous_scale _ _).measurable.comp measurable_snd))

attribute [local irreducible] MatrixNemytskii.state

theorem native_ae_state (hUs : StronglyMeasurable U) (p : P) :
    (fun x => native U (p,x)) =ᵐ[AddCircle.haarAddCircle (T := 2*Real.pi)]
      fun x => MatrixNemytskii.state U hUs (p,CircleNormalization.scale (2*Real.pi) 1 x) := by
  have he : (fun y => unit U (p,y)) =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
      fun y => MatrixNemytskii.state U hUs (p,y) :=
    (unit_ae U p).trans (MatrixNemytskii.state_ae U hUs p).symm
  change (fun x => unit U (p,CircleNormalization.scale (2*Real.pi) 1 x)) =ᵐ[_] _
  exact (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (p := fun y => unit U (p,y)=MatrixNemytskii.state U hUs (p,y)) he

/-- One common positive-heat subsequence realizes the full vector state
on parameter times space. It reuses the scalar bounded-arctangent
argument on a finite counting product, so no state moment is assumed. -/
theorem exists_subsequence (ν : Measure P) [IsFiniteMeasure ν] (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂ν.prod (AddCircle.haarAddCircle (T := 2*Real.pi)),
        Tendsto (fun j => VectorHeatMean.mean (U z.1) (ε (ns j),z.2)) atTop (𝓝 (native U z)) := by
  let W : P × Fin n → RealL2 := fun z => component U z.2 z.1
  have hW : Measurable W := measurable_from_prod_countable_left (fun i => component_measurable U hU i)
  obtain ⟨ns,hns,hae⟩ := HeatPhysicalSubsequence.exists_subsequence W hW (ν.prod Measure.count) ε hε
  have hp := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod hae)
  have hseq (j : ℕ) : Measurable (fun z : P × HeatCircle => VectorHeatMean.mean (U z.1) (ε (ns j),z.2)) :=
    Measurable.comp (g := fun z : VectorHeat.Physical (d := Fin n) × (ℝ × HeatCircle) => VectorHeatMean.mean z.1 z.2)
      (f := fun z : P × HeatCircle => (U z.1,(ε (ns j),z.2))) VectorHeatMean.measurable
      ((hU.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  refine ⟨ns,hns,(Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hseq (native_measurable U hU))).mpr ?_⟩
  filter_upwards [hp] with p hpoint
  have hi := Measure.ae_count_iff.mp hpoint
  filter_upwards [ae_all_iff.mpr hi] with x hx
  change Tendsto (fun j => WithLp.toLp 2 (fun i : Fin n => PhysicalProfile.physicalHeatMean
    (NativeHeatObservation.embed (component U i p)) (ε (ns j),x))) atTop
      (𝓝 (WithLp.toLp 2 (fun i : Fin n => PredictableScalarField.nativeField (component U i) (p,x))))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).tendsto _ |>.comp
    (tendsto_pi_nhds.mpr (fun i => hx i))

end Measurable
end SHEStochastic.VectorStateRepresentative
