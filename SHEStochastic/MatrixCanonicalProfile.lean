module

public import SHEStochastic.MatrixProfileFamily
public import SHEStochastic.MatrixProfileStability
public import SHEStochastic.VectorHeatMean

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixCanonicalProfile
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance MatrixProfileUpdate
  MatrixProfileFixedPoint
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ} {G : Coefficient (Fin n)}

structure Parameters (G : Coefficient (Fin n)) where
  holder : ℝ
  exponent : ℝ
  horizon : ℝ
  holder_nonneg : 0 ≤ holder
  exponent_pos : 0 < exponent
  exponent_le_one : exponent ≤ 1
  horizon_pos : 0 < horizon
  horizon_le_one : horizon ≤ 1
  holder_bound : ∀ z w, ‖G.value z-G.value w‖ ≤ holder*‖z-w‖^exponent
  small : contractionConstant G holder exponent*horizon^(exponent/4) ≤ 1/2

namespace Parameters
variable (P : Parameters G) {Z : Type*} [MeasurableSpace Z]

def family (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ) :
    Z × Domain → Matrix (Fin n) (Fin n) ℝ :=
  Classical.choose (MatrixProfileFamily.exists_family G Φ hΦ P.holder_nonneg P.exponent_pos
    P.horizon_pos P.horizon_le_one P.holder_bound P.small)

theorem family_measurable (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ) :
    Measurable (P.family Φ hΦ) :=
  (Classical.choose_spec (MatrixProfileFamily.exists_family G Φ hΦ P.holder_nonneg P.exponent_pos
    P.horizon_pos P.horizon_le_one P.holder_bound P.small)).1

theorem family_mem (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ) (p : Z × Domain) :
    P.family Φ hΦ p ∈ constraint G :=
  (Classical.choose_spec (MatrixProfileFamily.exists_family G Φ hΦ P.holder_nonneg P.exponent_pos
    P.horizon_pos P.horizon_le_one P.holder_bound P.small)).2.1 p

theorem family_fixed (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ)
    (z : Z) (r : ℝ) (hr : r ∈ Ioc 0 P.horizon) (x : SpatialCircle) :
    P.family Φ hΦ (z,(r,x)) = MatrixProfileUpdate.update G (fun q => Φ (z,q))
      (fun q => P.family Φ hΦ (z,q)) (⟨r,hr.1,hr.2.trans P.horizon_le_one⟩,x) := by
  have hf := (Classical.choose_spec (MatrixProfileFamily.exists_family G Φ hΦ P.holder_nonneg P.exponent_pos
    P.horizon_pos P.horizon_le_one P.holder_bound P.small)).2.2
  have he := congrFun hf (z,(r,x))
  simpa only [family,MatrixProfileFamily.update,canonicalUpdate,dif_pos hr] using he.symm

local instance : SecondCountableTopology (VectorHeat.Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (VectorHeat.Physical (d := Fin n)) := borel _
local instance : BorelSpace (VectorHeat.Physical (d := Fin n)) := ⟨rfl⟩

/-- The canonical coupled Gaussian profile at an actual vector spatial
L2 initial state; joint measurability is proved before random substitution. -/
def field : VectorHeat.Physical (d := Fin n) × Domain → Matrix (Fin n) (Fin n) ℝ :=
  P.family (fun p => VectorHeatMean.mean p.1 p.2) VectorHeatMean.measurable

theorem field_measurable : Measurable P.field :=
  P.family_measurable _ VectorHeatMean.measurable

theorem field_mem (p : VectorHeat.Physical (d := Fin n) × Domain) : P.field p ∈ constraint G :=
  P.family_mem _ VectorHeatMean.measurable p

theorem field_fixed (u : VectorHeat.Physical (d := Fin n)) (r : ℝ)
    (hr : r ∈ Ioc 0 P.horizon) (x : SpatialCircle) :
    P.field (u,(r,x)) = MatrixProfileUpdate.update G (VectorHeatMean.mean u)
      (fun q => P.field (u,q)) (⟨r,hr.1,hr.2.trans P.horizon_le_one⟩,x) :=
  P.family_fixed _ VectorHeatMean.measurable u r hr x

theorem field_l2_stability
    (hsmall : MatrixProfileStability.memoryConstant G P.holder P.exponent*
      SHE.ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4) ≤ 1/2)
    (u v : VectorHeat.Physical (d := Fin n)) :
    ∀ r ∈ Ioc 0 P.horizon,
      SHE.ProfileL2.normTwo AddCircle.haarAddCircle (fun x => ‖P.field (u,(r,x))-P.field (v,(r,x))‖) ≤
        2*(MatrixProfileStability.meanConstant G P.holder P.exponent*‖u-v‖)*r^((P.exponent-1)/4) := by
  intro r hr
  exact (MatrixProfileStability.l2_stability G P.holder_nonneg P.exponent_pos P.exponent_le_one
    P.horizon_pos P.horizon_le_one (norm_nonneg _) P.holder_bound
    (VectorHeatMean.mean u) (VectorHeatMean.mean v) (fun p => P.field (u,p)) (fun p => P.field (v,p))
    (P.field_measurable.comp (measurable_const.prodMk measurable_id))
    (P.field_measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => P.field_mem (u,p)) (fun p => P.field_mem (v,p))
    (fun s hs => VectorHeatMean.l2_difference hs.1 u v) hsmall (P.field_fixed u) (P.field_fixed v) r hr).1

theorem random_field_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : Ω → VectorHeat.Physical (d := Fin n)) (hU : Measurable U) :
    Measurable (fun p : Ω × Domain => P.field (U p.1,p.2)) :=
  P.field_measurable.comp ((hU.comp measurable_fst).prodMk measurable_snd)

end Parameters
end SHEStochastic.MatrixCanonicalProfile
