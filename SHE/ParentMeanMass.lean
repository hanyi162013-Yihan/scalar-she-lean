module

public import SHE.ParentMeanDensity
public import SHE.NativeHeatRoot

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ParentMeanDensity
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain OrderedHeatForests NativeHeatAction
  HistoryProductMeasure ScalarMeanEnvelope
open scoped BigOperators
local instance parentMeanMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

/-- Jointly Borel deterministic first-score density. The geometric old
parent product contains no sample-dependent Gaussian reference. -/
def globalDensity (k : ℕ) (p : History P k) (r : ℝ) (y : HeatCircle) : ℝ :=
  parentProduct L k p*∑ i : Fin (1+k),Real.sqrt ‖ProfileVariance.heatPhysical
    (4*(((carrier L k).observations.observations p i).target-r))
    ((carrier L k).observations.observations p i).center y‖

theorem globalDensity_nonneg (k : ℕ) (p : History P k) (r : ℝ) (y : HeatCircle) :
    0≤globalDensity L k p r y :=
  mul_nonneg (parentProduct_nonneg L k p) (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))

theorem globalDensity_variable_measurable (k : ℕ) (r : History P k→ℝ) (hr : Measurable r) :
    Measurable (fun z : History P k×HeatCircle=>globalDensity L k z.1 (r z.1) z.2) := by
  unfold globalDensity
  apply ((parentProduct_measurable L k).comp measurable_fst).mul
  apply Finset.measurable_sum
  intro i _
  have hT:=((carrier L k).observations.target_measurable i).comp
    (measurable_fst : Measurable (Prod.fst : History P k×HeatCircle→History P k))
  have hx:=((carrier L k).observations.center_measurable i).comp
    (measurable_fst : Measurable (Prod.fst : History P k×HeatCircle→History P k))
  exact Real.continuous_sqrt.measurable.comp
    (ProfileVariance.heatPhysical_joint_measurable.comp
      ((((hT.sub (hr.comp measurable_fst)).const_mul 4).prodMk hx).prodMk measurable_snd)).norm

def density (k : ℕ) (p : History P k) (r : ℝ) (y : HeatCircle) (x : Fin k→HeatCircle) : ℝ :=
  globalDensity L k (replaceSpace k p x) r y

theorem density_eq_parentEnvelope
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (r : ℝ) (y : HeatCircle) :
    density L k p r y=fun x=>parentEnvelope L hages k p hp x*
      ∑ i : Fin (1+k),Real.sqrt (terminalHeat L k p r y i x) := by
  funext x
  unfold density globalDensity
  rw [parentProduct_replaceSpace_eq L hages k p hp x]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [terminalHeat,congrFun (replaceSpace_targets L k p x) i]

theorem density_continuous
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) {r : ℝ}
    (hr : r<(carrier L k).terminal p) (y : HeatCircle) : Continuous (density L k p r y) := by
  rw [density_eq_parentEnvelope L hages k p hp]
  exact (parentEnvelope_continuous L hages k p hp).mul
    (continuous_finset_sum _ (fun i _=>Real.continuous_sqrt.comp
      (terminalHeat_continuous L hages k p hr y i)))

/-- Cauchy--Schwarz is applied to the unsquared parent density. Thus
only one assignment mass occurs, preserving every old interval power. -/
theorem parent_sqrt_single_root
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (i : Fin (1+k))
    {r : ℝ} (hr : r<(carrier L k).terminal p) (y : HeatCircle) :
    (∫ x : Fin k→HeatCircle,parentEnvelope L hages k p hp x*
      Real.sqrt (terminalHeat L k p r y i x) ∂Measure.pi (fun _=>AddCircle.haarAddCircle))≤
      ((Fintype.card (Choices 1 k):ℝ)*Real.sqrt ((Real.sqrt 2)^k)*NativeHeatSpan.sqrtKernelConstant)*
        ((L.observations.observations (rootParameter k p) 0).target-r)^(1/4:ℝ)*
        ‖ProfileVariance.heatPhysical (8*((L.observations.observations (rootParameter k p) 0).target-r))
          ((L.observations.observations (rootParameter k p) 0).center) y‖ := by
  let ν := Measure.pi (fun _ : Fin k=>AddCircle.haarAddCircle (T:=2*Real.pi))
  let Q := parentEnvelope L hages k p hp
  let E := terminalHeat L k p r y i
  have hQc := parentEnvelope_continuous L hages k p hp
  have hEc := terminalHeat_continuous L hages k p hr y i
  have hQi : Integrable Q ν := hQc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQEi : Integrable (fun x=>Q x*E x) ν :=
    (hQc.mul hEc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQn (x) : 0≤Q x := parentDensity_nonneg _ _ _ _ _ _
  have hs := ScoreSpatialCauchy.weighted_sqrt_integral ν Q E hQi hQEi hEc.measurable
    (ae_of_all _ hQn) (fun x=>norm_nonneg _)
  have hb := parent_spatial_bound L hages k p hp i hr y
  simp only [edge,NativeHeatSpan.kernel_eq_physical] at hb
  have hmass : (∫ x,Q x ∂ν)=(Fintype.card (Choices 1 k):ℝ) := parentEnvelope_mass L hages k p hp
  have hb' : (∫ x,Q x*E x ∂ν)≤(Fintype.card (Choices 1 k):ℝ)*(Real.sqrt 2)^k*
      ‖ProfileVariance.heatPhysical (4*((L.observations.observations (rootParameter k p) 0).target-r))
        ((L.observations.observations (rootParameter k p) 0).center) y‖ := by
    simpa only [Q,E,terminalHeat,parentEnvelope,Fin.sum_univ_one] using hb
  have hh := hs.2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb')
    (Real.sqrt_nonneg _))
  rw [hmass] at hh
  have hc : 0≤(Fintype.card (Choices 1 k):ℝ) := Nat.cast_nonneg _
  rw [mul_assoc (Fintype.card (Choices 1 k):ℝ),Real.sqrt_mul hc,←mul_assoc,
    Real.mul_self_sqrt hc,Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) k)] at hh
  have hw : 0<(L.observations.observations (rootParameter k p) 0).target-r :=
    sub_pos.mpr (root_target_after L hages k p hr 0)
  have hsqrt := mul_le_mul_of_nonneg_left (NativeHeatSpan.sqrt_kernel_four_eight hw
    ((L.observations.observations (rootParameter k p) 0).center) y)
    (mul_nonneg hc (Real.sqrt_nonneg ((Real.sqrt 2)^k)))
  exact hh.trans (by convert! hsqrt using 1 <;> ring)

/-- The deterministic common-reference density has exactly the same
native age-eight mass budget as the actual old-score density. -/
theorem density_mass_bound
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) {r : ℝ}
    (hr : r<(carrier L k).terminal p) (y : HeatCircle) :
    Integrable (density L k p r y) (Measure.pi (fun _ : Fin k=>AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k→HeatCircle,density L k p r y x ∂Measure.pi (fun _=>AddCircle.haarAddCircle))≤
        massBudget L k p 1 r y := by
  have hi (i : Fin (1+k)) : Integrable (fun x=>parentEnvelope L hages k p hp x*
      Real.sqrt (terminalHeat L k p r y i x)) (Measure.pi (fun _ : Fin k=>AddCircle.haarAddCircle)) :=
    ((parentEnvelope_continuous L hages k p hp).mul
      (Real.continuous_sqrt.comp (terminalHeat_continuous L hages k p hr y i))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine ⟨(density_continuous L hages k p hp hr y).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _),?_⟩
  rw [density_eq_parentEnvelope L hages k p hp]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _=>hi i)]
  have hs:=Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin (1+k))))=>
    parent_sqrt_single_root L hages k p hp i hr y)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,massBudget,one_mul,mul_assoc] using hs

end SHE.ParentMeanDensity
