module

public import SHE.ActualMeanKernelJoint

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers ControlledFutureFields ControlledFutureMeans StoppedGaussianScore PhysicalMeanRange
local instance actualControlledKernelJoint_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance actualControlledKernelJoint_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualControlledKernelJoint_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P X : Type} [MeasurableSpace P] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- A globally Borel formula for the compensated current mean. It agrees
with the literal future mean whenever the actual terminal derivative is
active; its extension outside that domain is harmless. -/
def explicitControlledMean (k : ℕ) (Λ : ℝ) (q : X → ℝ) (d : CircleL2)
    (Z D : X → CircleL2) (θ : X → ℝ) (x : X) (p : History P k) : WordRecursion.State (n+k) :=
  let T := fun i => ((carrier L k).observations.observations p i).target
  let a := fun i => NativeHeatSpan.unitCenter (((carrier L k).observations.observations p i).center)
  currentDirection T a (q x) (Z x)+θ x • explicitDirection Λ T a (q x) d (D x)

theorem explicitControlledMean_measurable (k : ℕ) (Λ : ℝ) (q : X → ℝ) (hq : Measurable q)
    (d : CircleL2) (Z D : X → CircleL2) (hZ : Measurable Z) (hD : Measurable D)
    (θ : X → ℝ) (hθ : Measurable θ) :
    Measurable (fun z : X × History P k => explicitControlledMean L k Λ q d Z D θ z.1 z.2) := by
  let T := fun z : X × History P k => fun i => ((carrier L k).observations.observations z.2 i).target
  let a := fun z : X × History P k => fun i => NativeHeatSpan.unitCenter (((carrier L k).observations.observations z.2 i).center)
  have hT (i : Fin (n+k)) : Measurable (fun z => T z i) :=
    ((carrier L k).observations.target_measurable i).comp measurable_snd
  have ha (i : Fin (n+k)) : Measurable (fun z => a z i) :=
    (CircleNormalization.continuous_scale (2*Real.pi) 1).measurable.comp
      (((carrier L k).observations.center_measurable i).comp measurable_snd)
  have hd := explicitDirection_measurable Λ T hT a ha (fun z => q z.1)
    (hq.comp measurable_fst) (fun _ => d) (fun z => D z.1) measurable_const (hD.comp measurable_fst)
  have hc : Measurable (fun z : X × History P k => currentDirection (T z) (a z) (q z.1) (Z z.1)) := by
    apply (WithLp.measurable_toLp 2 (Fin (n+k) → ℝ)).comp
    apply Measurable.of_eval
    intro i
    have hx := (CircleNormalization.continuous_scale 1 (2*Real.pi)).measurable.comp (ha i)
    exact PhysicalProfile.physicalHeatMean_joint_measurable.comp
      ((hZ.comp measurable_fst).prodMk (((hT i).sub (hq.comp measurable_fst)).prodMk hx))
  exact hc.add ((hθ.comp measurable_fst).smul hd)

theorem point_controlled_eq_explicit (k : ℕ) (Λ : ℝ) (q : X → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (u d : CircleL2) (Z D : X → CircleL2) (θ : X → ℝ)
    (x : X) (p : History P k) (y : HeatCircle) :
    point L k (q x) (controlledMean L k Λ (q x) (hq0 x) u d Z D (θ x) x) p y=
      point L k (q x) (explicitControlledMean L k Λ q d Z D θ x) p y := by
  by_cases hb : q x < (carrier L k).terminal p
  · have hgap : ∀ i, q x < ((carrier L k).observations.observations p i).target :=
      fun i => hb.trans_le ((carrier L k).targets_after p i)
    have he := futureMeanVector_affine Λ
      (fun i => ((carrier L k).observations.observations p i).target)
      (fun i => NativeHeatSpan.unitCenter (((carrier L k).observations.observations p i).center))
      (q x) (hq0 x) hgap u d (Z x) (D x) (θ x)
    rw [← explicitDirection_eq Λ _ _ (q x) (hq0 x) hgap d (D x)] at he
    simp only [point,if_pos hb,controlledMean,explicitControlledMean,he]
  · simp only [point,if_neg hb]

/-- Genuine joint measurability of the actual compensated kernel in the
terminal time, every old time, current random states, and spatial points.
This holds over any input sigma algebra for which q,Z,D,theta are
measurable, including a predictable sigma algebra when those data are. -/
theorem controlled_spatial_variable_measurable (k : ℕ) (Λ : ℝ) (q : X → ℝ)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (u d : CircleL2)
    (Z D : X → CircleL2) (hZ : Measurable Z) (hD : Measurable D)
    (θ : X → ℝ) (hθ : Measurable θ) (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (fun z : X × (HeatCircle × P) =>
      spatial L k (q z.1) (controlledMean L k Λ (q z.1) (hq0 z.1) u d Z D (θ z.1))
        (t z.1) z.1 z.2.1 z.2.2) := by
  have hh := spatial_variable_measurable L k q hq (explicitControlledMean L k Λ q d Z D θ)
    (explicitControlledMean_measurable L k Λ q hq d Z D hZ hD θ hθ) t ht
  have he : (fun z : X × (HeatCircle × P) =>
      spatial L k (q z.1) (controlledMean L k Λ (q z.1) (hq0 z.1) u d Z D (θ z.1))
        (t z.1) z.1 z.2.1 z.2.2)=fun z =>
      spatial L k (q z.1) (explicitControlledMean L k Λ q d Z D θ) (t z.1) z.1 z.2.1 z.2.2 := by
    funext z
    unfold spatial
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun p => point_controlled_eq_explicit L k Λ q hq0 u d Z D θ z.1 _ z.2.1)
  rw [he]
  exact hh

end SHE.ActualMeanKernel
