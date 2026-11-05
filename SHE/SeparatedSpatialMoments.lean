module

public import SHE.ScalarMeanSpatialMoments
public import SHE.SeparatedMeanBounds

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

/-- Spatial Jensen for the actual q-covariance and q-current mean with
the direction heat row at a separate later time r. The envelope and its
mass use r; the Gaussian law is never shifted. -/
theorem row_spatial_moment_of_point_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (t : Fin k → ℝ) (p : P) (W D C : ℝ) (hW : 0 ≤ W) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (m : Ω → History P k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History P k => m z.1 z.2))
    (q r : ℝ) (b : HeatCircle) (order : ℕ) (horder : 0 < order)
    (hp : StrictHistory L k (separated k (p,t,fun _ => (0:HeatCircle))))
    (hr : r < (carrier L k).terminal (separated k (p,t,fun _ => (0:HeatCircle))))
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k (separated k (p,t,fun _ => (0:HeatCircle))) x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k (separated k (p,t,fun _ => (0:HeatCircle))) x ≤
        W*parentEnvelope L hages k (separated k (p,t,fun _ => (0:HeatCircle))) hp x)
    (hpoint : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      (∫ ω,|rowPoint L k q r (m ω) (separated k (p,t,x)) b|^(2*order) ∂μ) ≤
        C*(D*density L c k (separated k (p,t,fun _ => (0:HeatCircle))) r b x)^(2*order)) :
    Integrable (fun ω => ‖rowSpatial L k q r m t ω b p‖^(2*order)) μ ∧
      (∫ ω,‖rowSpatial L k q r m t ω b p‖^(2*order) ∂μ) ≤
        C*(D*massBudget L k (separated k (p,t,fun _ => (0:HeatCircle))) W r b)^(2*order) := by
  let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
  let F := fun z : Ω × (Fin k → HeatCircle) => rowPoint L k q r (m z.1) (separated k (p,t,z.2)) b
  have hpM : Measurable (fun z : Ω × (Fin k → HeatCircle) => separated k (p,t,z.2)) :=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_snd))
  have hF : Measurable F := (rowPoint_variable_measurable L k (fun _ : Ω => q) (fun _ => r) measurable_const measurable_const m hm).comp
    ((measurable_fst.prodMk hpM).prodMk measurable_const)
  obtain ⟨B,hB,hcoarse⟩ := rowPoint_uniform_bound L (X:=Ω) T hT k q r t
  have hi (x : Fin k → HeatCircle) : Integrable (fun ω => |F (ω,x)|^(2*order)) μ := by
    have hf := ((hF.comp (measurable_id.prodMk (measurable_const (a := x)))).norm).pow_const (2*order)
    apply (integrable_const (B^(2*order))).mono' (by simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using hf.aestronglyMeasurable)
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoarse m ω b p x) _)
  have hden := density_mass_bound L c hc hages k p₀ hp W hW hn hb hr b
  have hdenM := density_measurable L c hc hages k p₀ hr b
  have hmain := WeightedSpatialMoments.nonnegative_envelope μ
    (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) F hF
    (fun x => D*density L c k p₀ r b x) (measurable_const.mul hdenM) (hden.1.const_mul D)
    (fun x => mul_nonneg hD (density_nonneg L c k p₀ r b x)) order horder C hC
    (ae_of_all _ hi) hpoint
  have hMass : (∫ x : Fin k → HeatCircle,D*density L c k p₀ r b x
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤ D*massBudget L k p₀ W r b := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hden.2 hD
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (integral_nonneg (fun x => mul_nonneg hD (density_nonneg L c k p₀ r b x))) hMass (2*order)) hC
  constructor
  · simpa only [rowSpatial,F,Complex.norm_real,Real.norm_eq_abs] using hmain.1
  · simpa only [rowSpatial,F,Complex.norm_real,Real.norm_eq_abs] using hmain.2.trans hpow

end SHE.ScalarMeanEnvelope
