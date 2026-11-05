module

public import SHE.ActualRawNoise
public import SHE.JointWordObserve
public import SHE.PredictableClock
public import SHE.HilbertParameterAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers HistoryProductMeasure NativeRandomKernel
open scoped ENNReal NNReal
local instance actualJointKernel_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance actualJointKernel_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance actualJointKernel_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance actualJointKernel_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualJointKernel_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance actualJointKernel_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance actualJointKernel_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
variable {X P : Type} [MeasurableSpace X] [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The current two-state joint mean, with every original stop retained
in its exponential and every original target retained in its heat age.
Outside the active kernel domain it is only a Borel extension. -/
def currentJointMean (k : ℕ) (Λ : ℝ) (q : X → ℝ)
    (U V : X → CircleL2) (x : X) (p : History P k) : WordRecursion.State (n+k) :=
  WithLp.toLp 2 (fun i =>
    let o := (carrier L k).observations.observations p i
    let u := PhysicalProfile.physicalHeatMean (U x) (o.target-q x,o.center)
    let v := PhysicalProfile.physicalHeatMean (V x) (o.target-q x,o.center)
    u+Real.exp (-Λ*(o.stop-q x))*(v-u))

theorem currentJointMean_measurable (k : ℕ) (Λ : ℝ) (q : X → ℝ) (hq : Measurable q)
    (U V : X → CircleL2) (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun z : X × History P k => currentJointMean L k Λ q U V z.1 z.2) := by
  apply (WithLp.measurable_toLp 2 (Fin (n+k) → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT := ((carrier L k).observations.target_measurable i).comp
    (measurable_snd : Measurable (Prod.snd : X × History P k → History P k))
  have hx := ((carrier L k).observations.center_measurable i).comp
    (measurable_snd : Measurable (Prod.snd : X × History P k → History P k))
  have hs := ((carrier L k).observations.stop_measurable i).comp
    (measurable_snd : Measurable (Prod.snd : X × History P k → History P k))
  have harg := (hT.sub (hq.comp measurable_fst)).prodMk hx
  have hu := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hU.comp measurable_fst).prodMk harg)
  have hv := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hV.comp measurable_fst).prodMk harg)
  exact hu.add ((((hs.sub (hq.comp measurable_fst)).const_mul (-Λ)).exp).mul (hv.sub hu))

/-- On the active domain the Borel extension is exactly the literal
physical joint observation. In particular no point evaluation of a
current L2 state is introduced. -/
theorem currentJointMean_eq_evaluate (k : ℕ) (Λ q : ℝ)
    (U V : ℝ → CircleL2) (XU XV : ℝ × HeatCircle → ℝ)
    (p : History P k) (hq : q < (carrier L k).terminal p) :
    currentJointMean L k Λ (fun _ : Unit => q) (fun _ => U q) (fun _ => V q) () p=
      JointWordObserve.evaluate Λ U V XU XV ((carrier L k).observations.observations p) q := by
  apply PiLp.ext
  intro i
  have ht := hq.trans_le ((carrier L k).targets_after p i)
  simp only [currentJointMean,JointWordObserve.evaluate,WithLp.ofLp_toLp,observe,ite_eq_left ht]

theorem point_joint_eq_current (k : ℕ) (Λ q : ℝ)
    (U V : ℝ → CircleL2) (XU XV : ℝ × HeatCircle → ℝ)
    (p : History P k) (y : HeatCircle) :
    point L k q (fun z => JointWordObserve.evaluate Λ U V XU XV
        ((carrier L k).observations.observations z) q) p y=
      point L k q (currentJointMean L k Λ (fun _ : Unit => q)
        (fun _ => U q) (fun _ => V q) ()) p y := by
  by_cases hq : q < (carrier L k).terminal p
  · simp only [point,ite_eq_left hq,currentJointMean_eq_evaluate L k Λ q U V XU XV p hq]
  · simp only [point,ite_eq_right hq]

variable (L₀ : CutoffWordLevel.Level R HeatCircle n)

def jointVariableField (k : ℕ) (Λ : ℝ) (q : X → ℝ) (U V : X → CircleL2)
    (t : X → Fin k → ℝ) (z : X × (HeatCircle × HeatCircle)) : ℂ :=
  spatial L₀ k (q z.1) (currentJointMean L₀ k Λ q U V) (t z.1) z.1 z.2.1 z.2.2

theorem jointVariableField_measurable (k : ℕ) (Λ : ℝ) (q : X → ℝ) (hq : Measurable q)
    (U V : X → CircleL2) (hU : Measurable U) (hV : Measurable V)
    (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (jointVariableField L₀ k Λ q U V t) :=
  spatial_variable_measurable L₀ k q hq (currentJointMean L₀ k Λ q U V)
    (currentJointMean_measurable L₀ k Λ q hq U V hU hV) t ht

/-- The original physical joint-flow kernel, averaged over old spatial
sites, is precisely the current-state kernel used for predictability. -/
theorem spatial_joint_eq_current (k : ℕ) (Λ q : ℝ)
    (U V : X → ℝ → CircleL2) (XU XV : X → ℝ × HeatCircle → ℝ)
    (t : Fin k → ℝ) (x : X) (y p : HeatCircle) :
    spatial L₀ k q (fun x z => JointWordObserve.evaluate Λ (U x) (V x) (XU x) (XV x)
      ((carrier L₀ k).observations.observations z) q) t x y p=
      jointVariableField L₀ k Λ (fun _ => q) (fun x => U x q) (fun x => V x q)
        (fun _ => t) (x,(y,p)) := by
  unfold spatial jointVariableField
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => point_joint_eq_current L₀ k Λ q (U x) (V x) (XU x) (XV x)
    (separated k (p,t,z)) y)

def jointRawNoiseColumns (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (U V : X → CircleL2) (t : X → Fin k → ℝ)
    (ell M : ℝ) (hell : 0 < ell) (c d : X → FiniteHaar.EllipticField ell M) :
    X → SignedKernelColumns.Space :=
  SignedKernelColumns.rawColumns (jointVariableField L₀ k Λ q U V t) Λ ρ hΛ hρ ell M hell c d

/-- Genuine raw countable-column measurability for the actual current
joint states. The theorem is valid for the predictable sigma algebra as
well as for Borel parameters, with no supplied scalar kernel hypothesis. -/
theorem jointRawNoiseColumns_measurable (T : ℝ) (hT : ∀ p,L₀.terminal p=T)
    (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (hq : Measurable q) (U V : X → CircleL2)
    (hU : Measurable U) (hV : Measurable V) (t : X → Fin k → ℝ) (ht : Measurable t)
    (ell M : ℝ) (hell : 0 < ell) (c d : X → FiniteHaar.EllipticField ell M)
    (hc : Measurable c) (hd : Measurable d) :
    Measurable (jointRawNoiseColumns L₀ k Λ ρ hΛ hρ q U V t ell M hell c d) := by
  apply SignedKernelColumns.rawColumns_measurable
    (jointVariableField_measurable L₀ k Λ q hq U V hU hV t ht) _ hΛ hρ hell c d hc hd
  intro x
  obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L₀ (Ω:=X) T hT k (q x) (t x)
  exact ⟨B,hB,fun y z => hbound (currentJointMean L₀ k Λ q U V) x y z⟩

end SHE.ActualMeanKernel
