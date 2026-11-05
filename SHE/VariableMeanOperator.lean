module

public import SHE.WeightedMeanOperator
public import SHE.NativeRealNoise
public import SHE.MeanInputReal
public import SHE.HeatedCurrentInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure NativeRandomKernel
local instance variableMeanOperator_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω A : Type} [MeasurableSpace Ω]
variable (R : A→ReferenceData) (L : (a : A)→CutoffWordLevel.Level (R a) HeatCircle 1)

/-- The literal weighted spatial kernel with sample-dependent reference
data and sample-dependent Gaussian mean. The reference is kept fixed
within each physical sample while only its direction-row age changes. -/
def familyWeightedField (a : Ω→A) (k : ℕ) (damping q r : Ω→ℝ)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (t : Ω→Fin k→ℝ) (z : Ω×NormalizedKernelSplit.Space) : ℂ :=
  weightedSpatial (L (a z.1)) k (damping z.1) (q z.1) (r z.1)
    (fun _ : Unit=>m z.1) (t z.1) () z.2.1 z.2.2

/-- The exact signed right-heat factorization is valid sample by
sample even when the reference profile depends on the entire past.
No conditional Gaussian law or covariance replacement is used here. -/
theorem family_weighted_operator_split (a : Ω→A) (k : ℕ) (damping q r T : Ω→ℝ)
    (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : ∀ z,Measurable (m z)) (t : Ω→Fin k→ℝ)
    (hqr : ∀ z,q z≤r z)
    (hr : ∀ z,r z<fixedTerminal (R:=R (a z)) (T z) k (t z)) (z : Ω) :
    integralOperator (familyWeightedField R L a k damping q q m t) z=
      (integralOperator (familyWeightedField R L a k damping q r m t) z).comp
        (circleHeatOperator (r z-q z) (sub_nonneg.mpr (hqr z))) := by
  have hm' : Measurable (fun p : Unit×History HeatCircle k=>m z p.2) := (hm z).comp measurable_snd
  have hh := weighted_operator_split (L (a z)) (T z) (hT z) k (hdamping z) (q z) (r z)
    (fun _ : Unit=>m z) hm' (t z) (hqr z) (hr z) ()
  exact hh

theorem family_weighted_input_split (a : Ω→A) (k : ℕ) (damping q r T : Ω→ℝ)
    (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : ∀ z,Measurable (m z)) (t : Ω→Fin k→ℝ)
    (hqr : ∀ z,q z≤r z)
    (hr : ∀ z,r z<fixedTerminal (R:=R (a z)) (T z) k (t z))
    (V : Ω→DyadicApproximation.RealL2) (z : Ω) :
    integralOperator (familyWeightedField R L a k damping q q m t) z (NativeHeatObservation.embed (V z))=
      integralOperator (familyWeightedField R L a k damping q r m t) z
        (HeatedCurrentInput.value (r z-q z) V z) := by
  rw [family_weighted_operator_split R L a k damping q r T hT hdamping m hm t hqr hr z,
    ContinuousLinearMap.comp_apply,←NativeHeatObservation.embed_heat (sub_nonneg.mpr (hqr z))]
  rfl

/-- The variable-reference operator is still literally the entire
physical mean mark on each sample, with the same old profile and all
original stop weights. -/
theorem family_weighted_mean_coordinate_ae (a : Ω→A) (k : ℕ) (damping q T : Ω→ℝ)
    (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : ∀ z,Measurable (m z)) (t : Ω→Fin k→ℝ)
    (hq : ∀ z,q z<fixedTerminal (R:=R (a z)) (T z) k (t z))
    (V : Ω→CircleL2) (z : Ω) :
    ∀ᵐ x : HeatCircle ∂haarAddCircle,
      (integralOperator (familyWeightedField R L a k damping q q m t) z (V z) x).re=
      ∫ y : Fin k→HeatCircle,
        let p := separated k (x,t z,y)
        let Z := (carrier (L (a z)) k).observations.observations p
        fderiv ℝ (gaussianAverage (covariance (R (a z)).reference Z (q z)
          ((carrier (L (a z)) k).terminal p)) (UncutSmoothWords.test (L (a z)) k p)) (m z p)
          (PhysicalMeanRange.dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
            (fun i=>NativeHeatSpan.unitCenter (Z i).center) (q z) (damping z) (V z))
          ∂Measure.pi (fun _=>haarAddCircle) := by
  have hm' : Measurable (fun p : Unit×History HeatCircle k=>m z p.2) := (hm z).comp measurable_snd
  exact weighted_operator_mean_coordinate_ae (L (a z)) (T z) (hT z) k (hdamping z) (q z)
    (fun _ : Unit=>m z) hm' (t z) (hq z) () (V z)

theorem family_weighted_bound_sections (a : Ω→A) (k : ℕ) (damping q r T : Ω→ℝ)
    (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k)) (t : Ω→Fin k→ℝ) :
    ∀ z,∃ B : ℝ,0≤B ∧ ∀ y x,‖familyWeightedField R L a k damping q r m t (z,(y,x))‖≤B := by
  intro z
  obtain ⟨B,hB,hbound⟩ := weightedSpatial_uniform_bound (L (a z)) (X:=Unit) (T z) (hT z)
    k (hdamping z) (q z) (r z) (t z)
  exact ⟨B,hB,fun y x=>hbound (fun _ : Unit=>m z) () y x⟩

end SHE.ActualMeanKernel
