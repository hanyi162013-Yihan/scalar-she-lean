module

public import SHE.RootStrong

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.CircleMultiplier
open MeasureTheory AddCircle CircleHeat FiniteHaar
local instance haarReal_multiplierPeriodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem operator_real_ae (c : CircleL2) (U : ℝ)
    (hc : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, (v y).im = 0) :
    ∀ᵐ y ∂haarAddCircle, (operator c U hc v y).im = 0 := by
  filter_upwards [operator_ae c U hc v, hcReal, hv] with y hy hr hv
  rw [hy]
  simp [Complex.mul_im, hr, hv]

theorem inverseOperator_real_ae (c : CircleL2) (m : ℝ) (hm : 0 < m)
    (hc : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcReal : ∀ᵐ y ∂haarAddCircle, (c y).im = 0) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, (v y).im = 0) :
    ∀ᵐ y ∂haarAddCircle, (inverseOperator c m hm hc v y).im = 0 := by
  apply operator_real_ae (inverseCoefficient c m hm hc) (m⁻¹) (inverseCoefficient_bound c m hm hc) _ v hv
  filter_upwards [inverseCoefficient_ae c m hm hc, hcReal] with y hy hr
  rw [hy]
  simp [Complex.inv_im, hr]

theorem equivalence_symm_apply (c : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hcl : ∀ᵐ y ∂haarAddCircle, m ≤ (c y).re)
    (hcu : ∀ᵐ y ∂haarAddCircle, ‖c y‖ ≤ U) (v : CircleL2) :
    (equivalence c m U hm hcl hcu).symm v = inverseOperator c m hm hcl v := by
  apply (equivalence c m U hm hcl hcu).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (congrArg (fun A : CircleL2 →L[ℂ] CircleL2 => A v)
    (operator_comp_inverse c m U hm hcl hcu)).symm

end SHE.CircleMultiplier

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
open scoped ENNReal
local instance haarReal_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The actual closed real-valued subspace of physical circle `L²`. -/
def realCircleSpace : Submodule ℝ CircleL2 :=
  (Complex.imCLM.compLpL 2 (haarAddCircle (T := (1 : ℝ)))).ker

/-- The actual closed real-coordinate subspace of the common Haar input. -/
def realInputSpace : Submodule ℝ HaarInput :=
  ⨅ q : HaarNode, (Complex.imCLM.comp (lp.evalCLM ℝ (fun _ : HaarNode => ℂ) 2 q)).ker

theorem mem_realCircleSpace (v : CircleL2) : v ∈ realCircleSpace ↔
    ∀ᵐ y ∂haarAddCircle, (v y).im = 0 := by
  change Complex.imCLM.compLpL 2 (haarAddCircle (T := (1 : ℝ))) v = 0 ↔ _
  have hc := Complex.imCLM.coeFn_compLpL (p := 2) v
  constructor
  · intro h
    have hz : ⇑(Complex.imCLM.compLpL 2 (haarAddCircle (T := (1 : ℝ))) v) =ᵐ[haarAddCircle] 0 := by
      rw [h]
      exact Lp.coeFn_zero ℝ 2 haarAddCircle
    filter_upwards [hc, hz] with y hy hz
    change (Complex.imCLM.compLpL 2 (haarAddCircle (T := (1 : ℝ))) v) y = (v y).im at hy
    exact hy.symm.trans hz
  · intro h
    apply Lp.ext
    filter_upwards [hc, h, Lp.coeFn_zero ℝ 2 haarAddCircle] with y hy hv hz
    change (Complex.imCLM.compLpL 2 (haarAddCircle (T := (1 : ℝ))) v) y = (v y).im at hy
    rw [hy, hv, hz]
    rfl

theorem mem_realInputSpace (x : HaarInput) : x ∈ realInputSpace ↔ ∀ q : HaarNode, (x q).im = 0 := by
  rw [realInputSpace, Submodule.mem_iInf]
  rfl

theorem isClosed_realCircleSpace : IsClosed (realCircleSpace : Set CircleL2) :=
  (Complex.imCLM.compLpL 2 (haarAddCircle (T := (1 : ℝ)))).isClosed_ker

theorem factor_preserves_real (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (x : HaarInput) (hx : x ∈ realInputSpace) :
    factor f m U hm hfreal hfbound x ∈ realCircleSpace := by
  let P : ℕ → HaarInput := fun N => ∑ q ∈ nodesBelow N, lp.single 2 q (x q)
  have hp : Filter.Tendsto P Filter.atTop (nhds x) :=
    (lp.hasSum_single ENNReal.ofNat_ne_top x).comp nodesBelow_tendsto
  apply isClosed_realCircleSpace.mem_of_tendsto
    (((factor f m U hm hfreal hfbound).continuous.tendsto x).comp hp)
  apply Filter.Eventually.of_forall
  intro N
  change factor f m U hm hfreal hfbound (∑ q ∈ nodesBelow N, lp.single 2 q (x q)) ∈ realCircleSpace
  simp only [map_sum, factor_single_value]
  apply Submodule.sum_mem
  intro q hq
  have hr : x q = ((x q).re : ℂ) := by
    apply Complex.ext <;> simp [(mem_realInputSpace x).mp hx q]
  rw [hr]
  change ((x q).re : ℝ) • globalHaarColumn q f ∈ realCircleSpace
  exact realCircleSpace.smul_mem _ ((mem_realCircleSpace _).mpr (globalHaarColumn_real_ae q f hfreal))

theorem factorEquivalence_inverse_formula (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (v : CircleL2) :
    (factorEquivalence f m U hm hfreal hfbound).symm v =
      factorAnalysis f m U hm hfreal hfbound
        (CircleMultiplier.inverseOperator f m hm (hfbound.mono (fun _ h => h.1)) v) := by
  let R := CircleMultiplier.inverseOperator f m hm (hfbound.mono (fun _ h => h.1))
  have hc := congrArg (fun A : CircleL2 →L[ℂ] CircleL2 => A (R v)) (factor_covariance f m U hm hfreal hfbound)
  rw [ContinuousLinearMap.comp_apply, factor_adjoint] at hc
  have hi := congrArg (fun A : CircleL2 →L[ℂ] CircleL2 => A v)
    (CircleMultiplier.operator_comp_inverse f m U hm (hfbound.mono (fun _ h => h.1))
      (CircleMultiplier.elliptic_norm_bound f m U hm hfreal hfbound))
  apply (factorEquivalence f m U hm hfreal hfbound).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, factorEquivalence_apply]
  exact (hc.trans hi).symm

theorem factor_inverse_preserves_real (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (v : CircleL2) (hv : v ∈ realCircleSpace) :
    (factorEquivalence f m U hm hfreal hfbound).symm v ∈ realInputSpace := by
  rw [factorEquivalence_inverse_formula]
  apply (mem_realInputSpace _).mpr
  intro q
  rw [factorAnalysis_apply]
  exact inner_real_fields_im _ _ (globalHaarColumn_real_ae q f hfreal)
    (CircleMultiplier.inverseOperator_real_ae f m hm (hfbound.mono (fun _ h => h.1)) hfreal v
      ((mem_realCircleSpace v).mp hv))

theorem innovationRotation_preserves_real (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (v : CircleL2) (hv : v ∈ realCircleSpace) :
    innovationRotation f m U hm hfreal hfbound v ∈ realInputSpace := by
  rw [innovationRotation_apply]
  apply factor_inverse_preserves_real f m U hm hfreal hfbound
  apply (mem_realCircleSpace _).mpr
  exact CircleMultiplier.operator_real_ae _ (Real.sqrt U)
    (CircleMultiplier.rootCoefficient_norm_bound f U (hfbound.mono (fun _ h => h.2)))
    (CircleMultiplier.rootCoefficient_real f U (hfbound.mono (fun _ h => h.2))) v
    ((mem_realCircleSpace v).mp hv)

@[simp] theorem innovationRotation_symm_apply (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (x : HaarInput) :
    (innovationRotation f m U hm hfreal hfbound).symm x =
      (CircleMultiplier.rootEquivalence f m U hm (hfbound.mono (fun _ h => h.1))
        (hfbound.mono (fun _ h => h.2))).symm (factorEquivalence f m U hm hfreal hfbound x) := rfl

theorem innovationRotation_inverse_preserves_real (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (x : HaarInput) (hx : x ∈ realInputSpace) :
    (innovationRotation f m U hm hfreal hfbound).symm x ∈ realCircleSpace := by
  rw [innovationRotation_symm_apply]
  change (CircleMultiplier.equivalence _ _ _ _ _ _).symm _ ∈ realCircleSpace
  rw [CircleMultiplier.equivalence_symm_apply]
  apply (mem_realCircleSpace _).mpr
  apply CircleMultiplier.inverseOperator_real_ae
  · exact CircleMultiplier.rootCoefficient_real f U (hfbound.mono (fun _ h => h.2))
  · exact (mem_realCircleSpace _).mp (factor_preserves_real f m U hm hfreal hfbound x hx)

/-- The innovation rotation restricts to an actual real orthogonal
isomorphism between real physical circle fields and real Haar inputs. -/
def realInnovationRotation (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hfbound : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    realCircleSpace ≃ₗᵢ[ℝ] realInputSpace where
  toFun v := ⟨innovationRotation f m U hm hfreal hfbound v.1,
    innovationRotation_preserves_real f m U hm hfreal hfbound v.1 v.2⟩
  invFun x := ⟨(innovationRotation f m U hm hfreal hfbound).symm x.1,
    innovationRotation_inverse_preserves_real f m U hm hfreal hfbound x.1 x.2⟩
  left_inv v := Subtype.ext ((innovationRotation f m U hm hfreal hfbound).symm_apply_apply v.1)
  right_inv x := Subtype.ext ((innovationRotation f m U hm hfreal hfbound).apply_symm_apply x.1)
  map_add' v w := Subtype.ext (map_add _ v.1 w.1)
  map_smul' r v := by
    apply Subtype.ext
    change innovationRotation f m U hm hfreal hfbound ((r : ℂ) • v.1) =
      (r : ℂ) • innovationRotation f m U hm hfreal hfbound v.1
    exact map_smul _ _ _
  norm_map' v := (innovationRotation f m U hm hfreal hfbound).norm_map v.1

end SHE.FiniteHaar
