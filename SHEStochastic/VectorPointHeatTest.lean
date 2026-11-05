module

public import SHEStochastic.VectorHeatObservation
public import SHE.ScalarHaarHeatRows
public import SHEStochastic.LpSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.VectorPointHeatTest
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem scalar_pairing {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) (u : RealL2) :
    inner ℝ (ScalarHaarHeatRows.test τ x) u=NativeHeatObservation.functional τ x u := by
  have he : (inner ℂ (realEmbed (ScalarHaarHeatRows.test τ x)) (realEmbed u)).re=
      inner ℝ (ScalarHaarHeatRows.test τ x) u := by
    rw [L2.inner_def,L2.inner_def]
    change RCLike.re (∫ y, inner ℂ (realEmbed (ScalarHaarHeatRows.test τ x) y) (realEmbed u y) ∂μ)=_
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (realEmbed (ScalarHaarHeatRows.test τ x)) (realEmbed u))]
    apply integral_congr_ae
    filter_upwards [realEmbed_ae (ScalarHaarHeatRows.test τ x),realEmbed_ae u] with y ht hu
    simp only [ht,hu,RCLike.inner_apply,Complex.conj_ofReal,← Complex.ofReal_mul,
      conj_trivial]
    rfl
  rw [ScalarHaarHeatRows.embed_test hτ x] at he
  have hp := CircleNormalization.push.inner_map_map
    (CircleNormalization.push.symm (circleHeat τ x)) (realEmbed u)
  rw [LinearIsometryEquiv.apply_symm_apply] at hp
  rw [← he]
  exact congrArg Complex.re hp.symm

/-- Literal vector heat feature: the scalar heat kernel placed in the
specified state component. The circle rescaling is part of the formula. -/
def test (τ : ℝ) (x : HeatCircle) (i : d) : VectorHeat.Physical (d := d) :=
  (L2EuclideanCoordinates.injection i).compLpL 2 μ (ScalarHaarHeatRows.test τ x)

theorem scalar_ae {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) :
    ⇑(ScalarHaarHeatRows.test τ x) =ᵐ[μ] fun y =>
      (ProfileVariance.heatPhysical τ x (CircleNormalization.scale 1 (2*Real.pi) y)).re := by
  have hp := CircleNormalization.pull_ae 1 (2*Real.pi) (circleHeat τ x)
  have hh := (CircleNormalization.scale_measurePreserving 1 (2*Real.pi)).quasiMeasurePreserving.ae
    (ProfileVariance.heatPhysical_ae hτ x)
  have he := realEmbed_ae (ScalarHaarHeatRows.test τ x)
  rw [ScalarHaarHeatRows.embed_test hτ x] at he
  have hinv : CircleNormalization.push.symm (circleHeat τ x)=
      CircleNormalization.pull 1 (2*Real.pi) (circleHeat τ x) :=
    CircleNormalization.equivalence_symm_apply (2*Real.pi) 1 _
  rw [hinv] at he
  filter_upwards [he,hp,hh] with y hy hp hh
  have hc : (ScalarHaarHeatRows.test τ x y : ℂ)=
      ProfileVariance.heatPhysical τ x (CircleNormalization.scale 1 (2*Real.pi) y) :=
    hy.symm.trans (hp.trans hh.symm)
  exact congrArg Complex.re hc

theorem test_ae {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) (i : d) :
    ⇑(test τ x i) =ᵐ[μ] fun y => L2EuclideanCoordinates.injection i
      ((ProfileVariance.heatPhysical τ x (CircleNormalization.scale 1 (2*Real.pi) y)).re) := by
  filter_upwards [(L2EuclideanCoordinates.injection i).coeFn_compLpL (ScalarHaarHeatRows.test τ x),
    scalar_ae hτ x] with y hy hs
  exact hy.trans (congrArg (L2EuclideanCoordinates.injection i) hs)

theorem pairing {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) (i : d) (u : VectorHeat.Physical (d := d)) :
    inner ℝ (test τ x i) u=VectorHeatObservation.observation τ x u i := by
  rw [VectorHeatObservation.apply_component,← scalar_pairing hτ]
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(L2EuclideanCoordinates.injection i).coeFn_compLpL (ScalarHaarHeatRows.test τ x),
    L2EuclideanCoordinates.coordinates_ae μ u] with y hy hc
  change inner ℝ ((L2EuclideanCoordinates.injection i).compLpL 2 μ (ScalarHaarHeatRows.test τ x) y) (u y)=_
  rw [hy]
  change inner ℝ (L2EuclideanCoordinates.injection i (ScalarHaarHeatRows.test τ x y)) (u y)=
    inner ℝ (ScalarHaarHeatRows.test τ x y) (L2EuclideanCoordinates.coordinates μ u i y)
  rw [hc i]
  simp [L2EuclideanCoordinates.injection,real_inner_smul_left,EuclideanSpace.inner_single_left,mul_comm]

theorem riesz {τ : ℝ} (hτ : 0 < τ) (x : HeatCircle) (i : d) :
    test τ x i=VectorHeatObservation.test τ x i := by
  apply ext_inner_right ℝ
  intro u
  rw [pairing hτ,VectorHeatObservation.test_pairing]

theorem zero {τ : ℝ} (hτ : τ ≤ 0) (x : HeatCircle) (i : d) : test τ x i=0 := by
  simp only [test,ScalarHaarHeatRows.test,circleHeat,dite_eq_right (not_lt.mpr hτ),map_zero]
  change (L2EuclideanCoordinates.injection i).compLpL 2 μ ((Complex.reCLM.compLpL 2 μ) 0)=0
  rw [map_zero,map_zero]

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (VectorHeat.Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (VectorHeat.Physical (d := d)) := borel _
local instance : BorelSpace (VectorHeat.Physical (d := d)) := ⟨rfl⟩

theorem measurable (i : d) : Measurable (fun p : ℝ × HeatCircle => test p.1 p.2 i) := by
  let F : (ℝ × HeatCircle) × AddCircle (1 : ℝ) → EuclideanSpace ℝ d := fun p =>
    if 0 < p.1.1 then L2EuclideanCoordinates.injection i
      ((ProfileVariance.heatPhysical p.1.1 p.1.2 (CircleNormalization.scale 1 (2*Real.pi) p.2)).re) else 0
  have hp : Measurable (fun p : (ℝ × HeatCircle) × AddCircle (1 : ℝ) =>
      ((p.1.1,p.1.2),CircleNormalization.scale 1 (2*Real.pi) p.2)) :=
    measurable_fst.prodMk ((CircleNormalization.continuous_scale _ _).measurable.comp measurable_snd)
  have hF : Measurable F :=
    ((L2EuclideanCoordinates.injection i).continuous.measurable.comp
      (Complex.measurable_re.comp (ProfileVariance.heatPhysical_joint_measurable.comp hp))).ite
        (measurableSet_lt measurable_const measurable_fst.fst) measurable_const
  have hK (p : ℝ × HeatCircle) : ⇑(test p.1 p.2 i) =ᵐ[μ] fun y => F (p,y) := by
    by_cases ht : 0 < p.1
    · simpa only [F,if_pos ht] using test_ae ht p.2 i
    · rw [zero (not_lt.mp ht)]
      have hz : ⇑(0 : VectorHeat.Physical (d := d)) =ᵐ[μ] fun _ => 0 :=
        Lp.coeFn_zero (EuclideanSpace ℝ d) 2 μ
      simpa only [F,if_neg ht] using hz
  exact (LpSections.stronglyMeasurable_of_joint μ _ F hF.stronglyMeasurable hK).measurable

end SHEStochastic.VectorPointHeatTest
