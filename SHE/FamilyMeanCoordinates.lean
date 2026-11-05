module

public import SHE.FamilyMeanInput

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier NativeHeatObservation
  DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  NativeRandomKernel HistoryProductMeasure GaussianConvolution PhysicalMeanRange
local instance familyMeanCoordinates_period : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω A : Type} [MeasurableSpace Ω]
variable (R : A→ReferenceData) (L : (a : A)→CutoffWordLevel.Level (R a) HeatCircle 1)

/-- The original-stop physical mean mark, with only the old spaces averaged. -/
def familyMeanCoordinate (a : Ω→A) (k : ℕ) (damping q : Ω→ℝ)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k)) (t : Ω→Fin k→ℝ)
    (V : Ω→RealL2) (z : Ω) (x : HeatCircle) : ℝ :=
  ∫ y : Fin k→HeatCircle,
    let p:=separated k (x,t z,y)
    let Z:=(carrier (L (a z)) k).observations.observations p
    fderiv ℝ (gaussianAverage (covariance (R (a z)).reference Z (q z)
      ((carrier (L (a z)) k).terminal p)) (UncutSmoothWords.test (L (a z)) k p)) (m z p)
      (dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
        (fun i=>NativeHeatSpan.unitCenter (Z i).center) (q z) (damping z) (embed (V z)))
    ∂Measure.pi (fun _=>haarAddCircle)

theorem family_weighted_complex_coordinate_ae (a : Ω→A) (k : ℕ) (damping q T : Ω→ℝ)
    (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k)) (hm : ∀ z,Measurable (m z))
    (t : Ω→Fin k→ℝ) (hq : ∀ z,q z<fixedTerminal (R:=R (a z)) (T z) k (t z))
    (V : Ω→RealL2) (z : Ω) :
    ∀ᵐ x ∂haarAddCircle,
      integralOperator (familyWeightedField R L a k damping q q m t) z (embed (V z)) x=
        (familyMeanCoordinate R L a k damping q m t V z x : ℂ) := by
  let G : Unit×(HeatCircle×HeatCircle)→ℂ:=fun w=>
    familyWeightedField R L a k damping q q m t (z,w.2)
  have hm' : Measurable (fun p : Unit×History HeatCircle k=>m z p.2):=
    (hm z).comp measurable_snd
  have hG : Measurable G:=weightedField_measurable (L (a z)) k (damping z) (q z) (q z)
    (fun _ : Unit=>m z) hm' (t z)
  have hb:=family_weighted_bound_sections R L a k damping q q T hT hdamping m t z
  have hv : ∀ᵐ y ∂haarAddCircle,(embed (V z) y).im=0 := by
    apply CircleNormalization.push_ae_property _ (fun x : ℂ=>x.im=0)
    exact (realEmbed_ae (V z)).mono (fun y hy=>by
      change (realEmbed (V z) y).im=0
      rw [hy]
      exact Complex.ofReal_im _)
  have hreal:=NativeRealNoise.integralOperator_real hG (fun _ : Unit=>hb)
    (fun _ y x=>by simp only [G,familyWeightedField,weightedSpatial,Complex.ofReal_im]) () (embed (V z)) hv
  have hop : integralOperator G ()=
      integralOperator (familyWeightedField R L a k damping q q m t) z :=
    (NativeRealNoise.integralOperator_section _ z).symm
  rw [hop] at hreal
  filter_upwards [family_weighted_mean_coordinate_ae R L a k damping q T hT hdamping
    m hm t hq (fun z=>embed (V z)) z,hreal] with x hre him
  apply Complex.ext
  · exact hre
  · simpa only [Complex.ofReal_im] using him

theorem familyMeanInput_fourier (a : Ω→A) (k : ℕ) (mass ρ : ℝ)
    (hmass : 1≤mass) (hρ : 0≤ρ) (damping q T : Ω→ℝ)
    (hT : ∀ z p,(L (a z)).terminal p=T z) (hdamping : ∀ z,0≤damping z)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k)) (hm : ∀ z,Measurable (m z))
    (t : Ω→Fin k→ℝ) (hq : ∀ z,q z<fixedTerminal (R:=R (a z)) (T z) k (t z))
    (V : Ω→RealL2) (z : Ω) (n : ℤ) :
    fourierCoeff (familyMeanInput R L a k mass ρ hmass hρ damping q m t V z) n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        fourierCoeff (fun x=>(familyMeanCoordinate R L a k damping q m t V z x:ℂ)) n := by
  rw [familyMeanInput,OneInputOperator.besselHalf_fourierCoeff]
  congr 1
  exact congrFun (fourierCoeff_congr_ae
    (family_weighted_complex_coordinate_ae R L a k damping q T hT hdamping m hm t hq V z)) n

end SHE.ActualMeanKernel
