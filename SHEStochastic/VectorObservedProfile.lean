module

public import SHEStochastic.VectorPhysicalRootTest
public import SHEStochastic.AveragedHeatCorrelation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.VectorObservedProfile
open MeasureTheory SHE SHE.StoppedFourier SHE.GaussianIncrement MatrixInfiniteHaar
open scoped ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

def difference (φ : State n → ℝ) (ε : ℝ) (U V : Ω → Physical (d := Fin n)) (p : Ω×HeatCircle) : ℝ :=
  φ (VectorHeatObservation.observation ε p.2 (V p.1))-
    φ (VectorHeatObservation.observation ε p.2 (U p.1))

theorem measurable (φ : State n → ℝ) (hφ : Measurable φ) {ε : ℝ} (hε : 0 < ε)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) :
    Measurable (difference φ ε U V) := by
  have hObs (A : Ω → Physical (d := Fin n)) (hA : Measurable A) :
      Measurable (fun p : Ω×HeatCircle => VectorHeatObservation.observation ε p.2 (A p.1)) :=
    Measurable.comp
      (g := fun q : HeatCircle×Physical (d := Fin n) => VectorHeatObservation.observation ε q.1 q.2)
      (f := fun p : Ω×HeatCircle => (p.2,A p.1))
      (VectorPhysicalRootTest.observation_measurable hε)
      (measurable_snd.prodMk (hA.comp measurable_fst))
  exact (hφ.comp (hObs V hV)).sub (hφ.comp (hObs U hU))

theorem bound (φ : State n → ℝ) {M : ℝ} (hφ : ∀ z,|φ z| ≤ M)
    (ε : ℝ) (U V : Ω → Physical (d := Fin n)) (p : Ω×HeatCircle) :
    |difference φ ε U V p| ≤ 2*M :=
  ((abs_sub _ _).trans (add_le_add (hφ _) (hφ _))).trans_eq (by ring)

/-- Signed correlation of the actual heat-observed coefficient
difference controls its canonical massive negative spatial energy. -/
theorem energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : State n → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V)
    {C Λ ρ : ℝ} (hC : 0 ≤ C)
    (hCorr : ∀ x y : HeatCircle,|∫ r : HeatCircle×Ω,
      difference φ ε U V (r.2,x+r.1)*difference φ ε U V (r.2,y+r.1)
        ∂AddCircle.haarAddCircle.prod μ| ≤ C)
    (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) :
    Integrable (fun ω => ‖NativeBesselFieldAE.value Λ ρ hΛ hρ.le
      (fun p => (difference φ ε U V p : ℂ)) ω‖^2) μ ∧
      (∫ ω,‖NativeBesselFieldAE.value Λ ρ hΛ hρ.le
        (fun p => (difference φ ε U V p : ℂ)) ω‖^2 ∂μ) ≤ Λ^(-ρ)*C :=
  AveragedHeatCorrelation.field μ (difference φ ε U V) (measurable φ hφ hε U V hU hV)
    (mul_nonneg (by norm_num) hM) (fun ω x => bound φ hφb ε U V (ω,x)) hC hCorr hΛ hρ

end SHEStochastic.VectorObservedProfile
