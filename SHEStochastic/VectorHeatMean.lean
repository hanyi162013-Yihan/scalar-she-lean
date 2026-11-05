module

public import SHEStochastic.VectorHeat
public import SHE.NativeHeatObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.VectorHeatMean
open MeasureTheory SHE SHE.ProfileL2 SHE.StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology (VectorHeat.Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (VectorHeat.Physical (d := d)) := borel _
local instance : BorelSpace (VectorHeat.Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩

def mean (u : VectorHeat.Physical (d := d)) (p : ℝ × HeatCircle) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 (fun i => PhysicalProfile.physicalHeatMean
    (NativeHeatObservation.embed (VectorHeat.coordinates u i)) p)

theorem measurable : Measurable (fun p : VectorHeat.Physical (d := d) × (ℝ × HeatCircle) => mean p.1 p.2) := by
  apply ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm.continuous.measurable).comp
  apply measurable_pi_iff.mpr
  intro i
  have hc : Continuous (fun u : VectorHeat.Physical (d := d) =>
      NativeHeatObservation.embed (VectorHeat.coordinates u i)) :=
    NativeHeatObservation.embed.continuous.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : d => DyadicApproximation.RealL2) i).continuous.comp
        VectorHeat.coordinates.continuous)
  exact PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hc.measurable.comp measurable_fst).prodMk measurable_snd)

theorem norm_bound {r : ℝ} (hr : 0 < r) (u : VectorHeat.Physical (d := d)) (x : HeatCircle) :
    ‖mean u (r,x)‖ ≤ ‖circleHeat r (0 : HeatCircle)‖*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2,mul_pow,← VectorHeat.coordinates.norm_map u,PiLp.norm_sq_eq_of_L2,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb := NativeHeatObservation.functional_norm_bound r x (VectorHeat.coordinates u i)
  rw [NativeHeatObservation.functional_physical hr] at hb
  have hx : ‖circleHeat r x‖ = ‖circleHeat r (0 : HeatCircle)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (circleHeat_norm_sq_center r x 0)
  rw [hx] at hb
  simpa only [mean,WithLp.ofLp_toLp,Real.norm_eq_abs,mul_pow,sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) hb 2

theorem memLp {r : ℝ} (hr : 0 < r) (u : VectorHeat.Physical (d := d)) :
    MemLp (fun x => ‖mean u (r,x)‖) 2 AddCircle.haarAddCircle := by
  have hp : Measurable (fun x : HeatCircle => (u,(r,x))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hm := (measurable (d := d)).comp hp
  apply bounded_memLp hm.norm
  intro x
  change |‖mean u (r,x)‖| ≤ _
  rw [abs_of_nonneg (norm_nonneg _)]
  exact norm_bound hr u x

/-- The vector heat mean contracts the actual spatial L2 input, with
the scalar normalization and all vector components kept explicit. -/
theorem contraction {r : ℝ} (hr : 0 < r) (u : VectorHeat.Physical (d := d)) :
    normTwo AddCircle.haarAddCircle (fun x => ‖mean u (r,x)‖) ≤ ‖u‖ := by
  apply (sq_le_sq₀ (normTwo_nonneg _ _) (norm_nonneg _)).mp
  rw [normTwo_sq]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  change (∫ x : HeatCircle, ∑ i : d, ‖PhysicalProfile.physicalHeatMean
    (NativeHeatObservation.embed (VectorHeat.coordinates u i)) (r,x)‖^2 ∂AddCircle.haarAddCircle) ≤ ‖u‖^2
  rw [integral_finsetSum _ (fun i _ =>
    (PhysicalProfile.physicalHeatMean_memLp hr
      (NativeHeatObservation.embed (VectorHeat.coordinates u i))).norm.integrable_sq),
    ← VectorHeat.coordinates.norm_map u,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i hi
  have hb := PhysicalProfile.physicalHeatMean_contraction hr
    (NativeHeatObservation.embed (VectorHeat.coordinates u i))
  rw [NativeHeatObservation.embed_norm] at hb
  have hs := pow_le_pow_left₀ (normTwo_nonneg _ _) hb 2
  rw [normTwo_sq] at hs
  simpa only [mean,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs] using hs

theorem difference {r : ℝ} (hr : 0 < r) (u v : VectorHeat.Physical (d := d)) (x : HeatCircle) :
    mean u (r,x)-mean v (r,x)=mean (u-v) (r,x) := by
  apply PiLp.ext
  intro i
  simp only [PiLp.sub_apply,mean,WithLp.ofLp_toLp,map_sub]
  exact PhysicalProfile.physicalHeatMean_difference hr _ _ x

theorem l2_difference {r : ℝ} (hr : 0 < r) (u v : VectorHeat.Physical (d := d)) :
    MemLp (fun x => ‖mean u (r,x)-mean v (r,x)‖) 2 AddCircle.haarAddCircle ∧
      normTwo AddCircle.haarAddCircle (fun x => ‖mean u (r,x)-mean v (r,x)‖) ≤ ‖u-v‖ := by
  simp only [difference hr u v]
  exact ⟨memLp hr _,contraction hr _⟩

end SHEStochastic.VectorHeatMean
