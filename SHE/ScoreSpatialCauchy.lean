module

public import SHE.ScoreSpatialSections
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ScoreSpatialCauchy
open Set MeasureTheory
variable {X : Type*} [MeasurableSpace X]

/-- Weighted Cauchy--Schwarz preserves the positive old-score density
instead of squaring it and losing the time-gap exponents. Only AE
nonnegativity is needed for the genuine singular Gaussian score energies. -/
theorem weighted_sqrt_integral (ν : Measure X) (P E : X → ℝ)
    (hP : Integrable P ν) (hPE : Integrable (fun x => P x*E x) ν)
    (hE : Measurable E) (hPn : ∀ᵐ x ∂ν, 0 ≤ P x) (hEn : ∀ x, 0 ≤ E x) :
    Integrable (fun x => P x*Real.sqrt (E x)) ν ∧
      (∫ x,P x*Real.sqrt (E x) ∂ν) ≤
        Real.sqrt (∫ x,P x ∂ν)*Real.sqrt (∫ x,P x*E x ∂ν) := by
  let f := fun x => Real.sqrt (P x)
  let g := fun x => Real.sqrt (P x*E x)
  have hfm : AEStronglyMeasurable f ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hP.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hPE.aestronglyMeasurable
  have hfsq : (fun x => f x^2)=ᵐ[ν]P := by
    filter_upwards [hPn] with x hx
    exact Real.sq_sqrt hx
  have hgsq : (fun x => g x^2)=ᵐ[ν](fun x => P x*E x) := by
    filter_upwards [hPn] with x hx
    exact Real.sq_sqrt (mul_nonneg hx (hEn x))
  have hf : MemLp f 2 ν := (memLp_two_iff_integrable_sq hfm).mpr (hP.congr hfsq.symm)
  have hg : MemLp g 2 ν := (memLp_two_iff_integrable_sq hgm).mpr (hPE.congr hgsq.symm)
  have he : (fun x => f x*g x)=ᵐ[ν](fun x => P x*Real.sqrt (E x)) := by
    filter_upwards [hPn] with x hx
    dsimp only [f,g]
    rw [Real.sqrt_mul hx,← mul_assoc,Real.mul_self_sqrt hx]
  refine ⟨(hf.integrable_mul hg).congr he,?_⟩
  have hf' : MemLp f (ENNReal.ofReal (2:ℝ)) ν := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2:ℝ)) ν := by simpa using hg
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
  have hnf (x) : ‖f x‖=f x := Real.norm_of_nonneg (Real.sqrt_nonneg _)
  have hng (x) : ‖g x‖=g x := Real.norm_of_nonneg (Real.sqrt_nonneg _)
  simp only [hnf,hng,Real.rpow_two] at hh
  rw [integral_congr_ae he,integral_congr_ae hfsq,integral_congr_ae hgsq] at hh
  simpa only [Real.sqrt_eq_rpow] using hh

end SHE.ScoreSpatialCauchy

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry OrderedHeatForests NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The terminal first-score square root is averaged with the unsquared
old-score product. Original-parent integration keeps the correct old
interval powers and ends at the original root heat envelope. -/
theorem spatialScore_sqrt_endpoint (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (W : ℝ) (hW : 0 ≤ W)
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k p x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k p x ≤ W*parentEnvelope L hages k p hp x)
    (i : Fin (n+k)) {q : ℝ} (hq : q < (carrier L k).terminal p) (b : HeatCircle) :
    let t := fun j => ((carrier L k).observations.observations p j).target
    let E := fun x : Fin k → HeatCircle =>
      edge (4*(t i-q)) (mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i)))
        (((carrier L k).observations.observations (replaceSpace k p x) i).center) b
    Integrable (fun x => spatialScore L c k p x*Real.sqrt (E x))
        (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k → HeatCircle, spatialScore L c k p x*Real.sqrt (E x)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
      (W*(Fintype.card (Choices n k) : ℝ))*Real.sqrt ((Real.sqrt 2)^k*
        ∑ j : Fin n, edge (4*((L.observations.observations (rootParameter k p) j).target-q))
          (mul_pos (by norm_num) (sub_pos.mpr (root_target_after L hages k p hq j)))
          ((L.observations.observations (rootParameter k p) j).center) b) := by
  intro t E
  have hm := spatialScore_mass L c hc hages k p hp W hn hb
  have he := spatialScore_endpoint L c hc hages k p hp W hW hn hb i hq b
  have hE : Measurable E := by
    have heq : E = fun x =>
        edge (4*(t i-q)) (mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i)))
          (values (fun j => (L.observations.observations (rootParameter k p) j).center) k x i) b := by
      funext x
      exact congrArg (fun a => edge _ _ a b) (congrFun (replaceSpace_centers L k p x) i)
    rw [heq]
    exact ((continuous_edge _).comp
      (((continuous_apply i).comp (values_continuous _ k)).prodMk continuous_const)).measurable
  have hCS := ScoreSpatialCauchy.weighted_sqrt_integral _ _ E hm.1 he.1 hE hn (fun _ => norm_nonneg _)
  refine ⟨hCS.1,?_⟩
  have hh := mul_le_mul (Real.sqrt_le_sqrt hm.2) (Real.sqrt_le_sqrt he.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have ha : 0 ≤ W*(Fintype.card (Choices n k) : ℝ) := mul_nonneg hW (Nat.cast_nonneg _)
  have hs := (hCS.2.trans hh)
  rw [mul_assoc (Fintype.card (Choices n k) : ℝ),← mul_assoc W] at hs
  rw [Real.sqrt_mul ha,← mul_assoc,Real.mul_self_sqrt ha] at hs
  exact hs

end SHE.PhysicalScoreChain
