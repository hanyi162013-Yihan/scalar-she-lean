module

public import SHE.ScalarMeanEnvelope
public import SHE.ActualMeanPointBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain OrderedHeatForests NativeHeatAction
  HistoryProductMeasure ActualMeanKernel
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

def massBudget (k : ℕ) (p : History P k) (W q : ℝ) (b : HeatCircle) : ℝ :=
  ((1+k:ℕ):ℝ)*(W*(Fintype.card (Choices 1 k) : ℝ)*Real.sqrt ((Real.sqrt 2)^k)*NativeHeatSpan.sqrtKernelConstant)*
    ((L.observations.observations (rootParameter k p) 0).target-q)^(1/4:ℝ)*
      ‖ProfileVariance.heatPhysical (8*((L.observations.observations (rootParameter k p) 0).target-q))
        ((L.observations.observations (rootParameter k p) 0).center) b‖

/-- Actual spatial averaging of the literal random derivative retains
the precise deterministic density mass. Coarse point integrability and
all Borel conditions are derived; the displayed quantitative point moment
is the Gaussian-word input to this intermediate assembly theorem. -/
theorem spatial_moment_of_point_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (t : Fin k → ℝ) (p : P) (W D C : ℝ) (hW : 0 ≤ W) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (m : Ω → History P k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History P k => m z.1 z.2))
    (q : ℝ) (b : HeatCircle) (order : ℕ) (horder : 0 < order)
    (hp : StrictHistory L k (separated k (p,t,fun _ => (0:HeatCircle))))
    (hq : q < (carrier L k).terminal (separated k (p,t,fun _ => (0:HeatCircle))))
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k (separated k (p,t,fun _ => (0:HeatCircle))) x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k (separated k (p,t,fun _ => (0:HeatCircle))) x ≤
        W*parentEnvelope L hages k (separated k (p,t,fun _ => (0:HeatCircle))) hp x)
    (hpoint : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      (∫ ω,|point L k q (m ω) (separated k (p,t,x)) b|^(2*order) ∂μ) ≤
        C*(D*density L c k (separated k (p,t,fun _ => (0:HeatCircle))) q b x)^(2*order)) :
    Integrable (fun ω => ‖spatial L k q m t ω b p‖^(2*order)) μ ∧
      (∫ ω,‖spatial L k q m t ω b p‖^(2*order) ∂μ) ≤
        C*(D*massBudget L k (separated k (p,t,fun _ => (0:HeatCircle))) W q b)^(2*order) := by
  let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
  let F := fun z : Ω × (Fin k → HeatCircle) => point L k q (m z.1) (separated k (p,t,z.2)) b
  have hpM : Measurable (fun z : Ω × (Fin k → HeatCircle) => separated k (p,t,z.2)) :=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_snd))
  have hF : Measurable F := (point_measurable L k q m hm).comp
    ((measurable_fst.prodMk hpM).prodMk measurable_const)
  obtain ⟨B,hB,hcoarse⟩ := point_uniform_bound L (Ω:=Ω) T hT k q t
  have hi (x : Fin k → HeatCircle) : Integrable (fun ω => |F (ω,x)|^(2*order)) μ := by
    have hf := ((hF.comp (measurable_id.prodMk (measurable_const (a := x)))).norm).pow_const (2*order)
    apply (integrable_const (B^(2*order))).mono' (by simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using hf.aestronglyMeasurable)
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoarse m ω b p x) _)
  have hden := density_mass_bound L c hc hages k p₀ hp W hW hn hb hq b
  have hdenM := density_measurable L c hc hages k p₀ hq b
  have hmain := WeightedSpatialMoments.nonnegative_envelope μ
    (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) F hF
    (fun x => D*density L c k p₀ q b x) (measurable_const.mul hdenM) (hden.1.const_mul D)
    (fun x => mul_nonneg hD (density_nonneg L c k p₀ q b x)) order horder C hC
    (ae_of_all _ hi) hpoint
  have hMass : (∫ x : Fin k → HeatCircle,D*density L c k p₀ q b x
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤ D*massBudget L k p₀ W q b := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hden.2 hD
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (integral_nonneg (fun x => mul_nonneg hD (density_nonneg L c k p₀ q b x))) hMass (2*order)) hC
  constructor
  · simpa only [spatial,F,Complex.norm_real,Real.norm_eq_abs] using hmain.1
  · simpa only [spatial,F,Complex.norm_real,Real.norm_eq_abs] using hmain.2.trans hpow

end SHE.ScalarMeanEnvelope
