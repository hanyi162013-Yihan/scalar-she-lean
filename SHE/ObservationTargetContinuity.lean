module

public import SHE.HeatAgeContinuity
public import SHE.CanonicalConditional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.ObservationTargetContinuity
open Set Filter MeasureTheory StoppedFourier WordRecursion PhysicalProfile CanonicalConditional
open scoped Topology

theorem continuousAt_heatMean_age {t : ℝ} (ht : 0 < t) (u : CircleL2) (x : HeatCircle) :
    ContinuousAt (fun s : ℝ => physicalHeatMean u (s,x)) t := by
  have hh := (HeatAgeContinuity.continuousAt_circleHeat_age ht x).inner
    (𝕜 := ℂ) (continuousAt_const : ContinuousAt (fun _ : ℝ => u) t)
  have hc := Complex.continuous_re.continuousAt.comp hh
  have he : (fun s : ℝ => physicalHeatMean u (s,x))=ᶠ[𝓝 t]
      fun s => (inner ℂ (circleHeat s x) u).re := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact physicalHeatMean_eq hs u x
  exact hc.congr_of_eventuallyEq he

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

theorem continuous_initialMean (Z : X → Fin n → Observation) (centers : Fin n → HeatCircle)
    (hT : ∀ i,Continuous (fun p => (Z p i).target)) (hx : ∀ p i,(Z p i).center=centers i)
    (t : ℝ) (ht : ∀ p i,t < (Z p i).target) (u : CircleL2) :
    Continuous (fun p => initialMean (Z p) t u) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun p => physicalHeatMean u ((Z p i).target-t,(Z p i).center))
  simp_rw [hx]
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (continuousAt_heatMean_age (sub_pos.mpr (ht p i)) u (centers i)).comp
    (f := fun p => (Z p i).target-t) ((hT i).sub continuous_const).continuousAt

theorem continuous_observe (Z : X → Fin n → Observation) (centers : Fin n → HeatCircle)
    (hT : ∀ i,Continuous (fun p => (Z p i).target)) (hx : ∀ p i,(Z p i).center=centers i)
    (t : ℝ) (ht : ∀ p i,t < (Z p i).target)
    (U : ℝ → CircleL2) (Y : ℝ × HeatCircle → ℝ) :
    Continuous (fun p => observe U Y (Z p) t) := by
  have he : (fun p => observe U Y (Z p) t)=fun p => initialMean (Z p) t (U t) := by
    funext p
    ext i
    change (if t<(Z p i).target then physicalHeatMean (U t) ((Z p i).target-t,(Z p i).center)
      else Y (t,(Z p i).center))=_
    rw [if_pos (ht p i)]
    rfl
  rw [he]
  exact continuous_initialMean Z centers hT hx t ht (U t)

end SHE.ObservationTargetContinuity
