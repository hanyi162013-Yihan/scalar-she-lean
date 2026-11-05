module

public import SHE.PredictableL2

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MeasurableIsometryLift
open MeasureTheory
open scoped ENNReal

variable {X A B : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
variable [SecondCountableTopology B]
variable (μ : Measure X) (Φ : X → A →ₗᵢ[ℝ] B)
variable (hΦ : Measurable (fun p : X × A => Φ p.1 p.2))
include hΦ

theorem action_measurable (v : Lp A 2 μ) : Measurable (fun x => Φ x (v x)) :=
  hΦ.comp (measurable_id.prodMk (Lp.stronglyMeasurable v).measurable)

theorem action_memLp (v : Lp A 2 μ) : MemLp (fun x => Φ x (v x)) 2 μ :=
  (Lp.memLp v).of_le (action_measurable μ Φ hΦ v).stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (Φ x).norm_map (v x) |>.le))

def map (v : Lp A 2 μ) : Lp B 2 μ :=
  (action_memLp μ Φ hΦ v).toLp (fun x => Φ x (v x))

theorem map_ae (v : Lp A 2 μ) : map μ Φ hΦ v =ᵐ[μ] (fun x => Φ x (v x)) :=
  (action_memLp μ Φ hΦ v).coeFn_toLp

/-- A genuinely jointly measurable field of pointwise linear isometries
acts isometrically on the complete L² space. The sigma algebra can be
the predictable sigma algebra, without any operator-norm measurability. -/
def isometry : Lp A 2 μ →ₗᵢ[ℝ] Lp B 2 μ where
  toFun := map μ Φ hΦ
  map_add' v w := by
    apply Lp.ext
    filter_upwards [map_ae μ Φ hΦ (v+w),map_ae μ Φ hΦ v,map_ae μ Φ hΦ w,
      Lp.coeFn_add v w,Lp.coeFn_add (map μ Φ hΦ v) (map μ Φ hΦ w)] with x hs hv hw hsum hout
    rw [hs,hout]
    change Φ x ((v+w) x)=map μ Φ hΦ v x+map μ Φ hΦ w x
    rw [hsum]
    change Φ x (v x+w x)= _
    rw [map_add,hv,hw]
  map_smul' r v := by
    apply Lp.ext
    filter_upwards [map_ae μ Φ hΦ (r • v),map_ae μ Φ hΦ v,
      Lp.coeFn_smul r v,Lp.coeFn_smul r (map μ Φ hΦ v)] with x hs hv hsource hout
    simp only [RingHom.id_apply]
    rw [hs,hout]
    simp only [Pi.smul_apply,RingHom.id_apply]
    rw [hsource]
    change Φ x (r • v x)=r • map μ Φ hΦ v x
    rw [map_smul,hv]
  norm_map' v := by
    change ‖map μ Φ hΦ v‖=‖v‖
    rw [Lp.norm_def,Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [map_ae μ Φ hΦ v] with x hx
    rw [hx,(Φ x).norm_map]

end SHE.MeasurableIsometryLift
