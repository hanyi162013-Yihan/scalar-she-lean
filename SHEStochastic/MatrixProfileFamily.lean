module

public import SHEStochastic.MatrixHeatCovarianceFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixProfileFamily
open MeasureTheory Set MatrixNonlinearCoefficient MatrixHeatCovariance MatrixProfileUpdate
  MatrixProfileFixedPoint
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ} {Z : Type*} [MeasurableSpace Z] (G : Coefficient (Fin n))

def update (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) {h : ℝ} (hh1 : h ≤ 1)
    (κ : Z × Domain → Matrix (Fin n) (Fin n) ℝ) (p : Z × Domain) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalUpdate G (fun q => Φ (p.1,q)) hh1 (fun q => κ (p.1,q)) p.2

theorem measurable (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ)
    {h : ℝ} (hh1 : h ≤ 1) (κ : Z × Domain → Matrix (Fin n) (Fin n) ℝ)
    (hκ : Measurable κ) (hκS : ∀ p, κ p ∈ constraint G) :
    Measurable (update G Φ hh1 κ) := by
  classical
  let s : Set (Z × Domain) := {p | p.2.1 ∈ Ioc 0 h}
  have hp : Measurable (fun p : s => (p.val.1,
      ((⟨p.val.2.1,p.property.1,p.property.2.trans hh1⟩ : HeatCovarianceMeasure.Window),p.val.2.2))) :=
    (measurable_fst.comp measurable_subtype_coe).prodMk
      (((measurable_snd.fst.comp measurable_subtype_coe).subtype_mk).prodMk
        (measurable_snd.snd.comp measurable_subtype_coe))
  have hcov := MatrixHeatCovarianceFamily.measurable κ hκ (upper G) (fun p => (hκS p).2)
  have hmean : Measurable (fun p : Z × (HeatCovarianceMeasure.Window × SpatialCircle) =>
      Φ (p.1,(p.2.1.val,p.2.2))) := hΦ.comp
    (measurable_fst.prodMk ((measurable_subtype_coe.comp measurable_snd.fst).prodMk measurable_snd.snd))
  have hm := ((MatrixGaussianAverage.measurable G).comp (hcov.prodMk hmean)).comp hp
  exact hm.dite measurable_const (measurableSet_Ioc.preimage measurable_snd.fst)

/-- The full profile can be selected jointly measurably in an arbitrary
input parameter. The same complete bounded-function fixed point proof
is applied on the product parameter domain. -/
theorem exists_family (Φ : Z × Domain → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ)
    {K β h : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hh : 0 < h) (hh1 : h ≤ 1)
    (hG : ∀ z w, ‖G.value z-G.value w‖ ≤ K*‖z-w‖^β)
    (hsmall : contractionConstant G K β*h^(β/4) ≤ 1/2) :
    ∃ κ : Z × Domain → Matrix (Fin n) (Fin n) ℝ, Measurable κ ∧
      (∀ p, κ p ∈ constraint G) ∧ update G Φ hh1 κ = κ := by
  let q := contractionConstant G K β*h^(β/4)
  have hq : 0 ≤ q := mul_nonneg (contractionConstant_nonneg G hK) (Real.rpow_nonneg hh.le _)
  have hFS : ∀ κ, Measurable κ → (∀ p, κ p ∈ constraint G) →
      ∀ p, update G Φ hh1 κ p ∈ constraint G := fun κ _ _ p =>
    canonical_mem G (fun z => Φ (p.1,z)) hh1 (fun z => κ (p.1,z)) p.2
  apply BoundedMeasurableFixedPoint.exists_fixedPoint (constraint_closed G)
    (G.covariance 0) (baseline_mem G) (upper G) (fun _ hz => hz.2)
    (update G Φ hh1) (measurable G Φ hΦ hh1) hFS q hq (by dsimp [q]; linarith)
  intro κ η hκ hη hκS hηS D hD hDiff p
  exact canonical_contraction G (fun z => Φ (p.1,z)) hK hβ.le hh.le hh1 hG
    (fun z => κ (p.1,z)) (fun z => η (p.1,z))
    (hκ.comp (measurable_const.prodMk measurable_id))
    (hη.comp (measurable_const.prodMk measurable_id))
    (fun z => hκS (p.1,z)) (fun z => hηS (p.1,z)) hD (fun z => hDiff (p.1,z)) p.2

end SHEStochastic.MatrixProfileFamily
