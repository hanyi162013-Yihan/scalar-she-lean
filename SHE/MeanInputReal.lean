module

public import SHE.MeanInputFields
public import SHE.WeightedMeanInput
public import SHE.NativeRealNoise

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeBesselReal
open Set MeasureTheory AddCircle StoppedFourier
local instance meanInputReal_nativePositive0 : Fact (0<2*Real.pi) := ⟨by positivity⟩

theorem real_of_conjugate_eq (v : CircleL2) (hv : conjugate v=v) :
    ∀ᵐ x ∂haarAddCircle,(v x).im=0 := by
  have ha := conjugate_ae v
  rw [hv] at ha
  filter_upwards [ha] with x hx
  have hh := congrArg Complex.im hx
  simp only [Complex.conj_im] at hh
  linarith

/-- Genuine vector integration preserves the native real subspace.
The nonintegrable zero extension of the Bochner integral is covered. -/
theorem integral_real {A : Type*} [MeasurableSpace A] (ν : Measure A) (F : A→CircleL2)
    (hF : ∀ a,∀ᵐ x ∂haarAddCircle,(F a x).im=0) :
    ∀ᵐ x ∂haarAddCircle,((∫ a,F a ∂ν) x).im=0 := by
  apply real_of_conjugate_eq
  by_cases hi : Integrable F ν
  · rw [←conjugate.integral_comp_comm hi]
    exact integral_congr_ae (ae_of_all _ (fun a=>conjugate_eq_of_real _ (hF a)))
  · rw [integral_undef hi,map_zero]

end SHE.NativeBesselReal

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel HistoryProductMeasure GaussianConvolution PhysicalMeanRange
local instance meanInputReal_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

theorem weighted_operator_mean_coordinate_ae (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q : ℝ)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2)) (t : Fin k→ℝ)
    (hq : q<fixedTerminal (R:=R) T k t) (ω : Ω) (v : CircleL2) :
    ∀ᵐ p : HeatCircle ∂haarAddCircle,
      (integralOperator (weightedField L k Λ q q m t) ω v p).re=
      ∫ z : Fin k→HeatCircle,
        let a := separated k (p,t,z)
        let Z := (carrier L k).observations.observations a
        fderiv ℝ (gaussianAverage (covariance R.reference Z q ((carrier L k).terminal a))
          (UncutSmoothWords.test L k a)) (m ω a)
          (dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
            (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ v)
          ∂Measure.pi (fun _=>haarAddCircle) := by
  obtain ⟨B,hB,hbound⟩ := weightedSpatial_uniform_bound L (X:=Ω) T hT k hΛ q q t
  filter_upwards [integralOperator_ae (weightedField_measurable L k Λ q q m hm t) hB
    (fun z y p=>hbound m z y p) ω v] with p hp
  rw [hp]
  exact weightedSpatial_mean_input L T hT k hΛ q m hm t hq ω p v

theorem meanInput_real (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) {Λ : ℝ} (hΛ : 0≤Λ) (q : ℝ)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2))
    (V : Ω→RealL2) (t : Fin k→ℝ) (ω : Ω) :
    ∀ᵐ p : HeatCircle ∂haarAddCircle,(meanInput L k mass ρ hmass hρ Λ q m V (t,ω) p).im=0 := by
  apply NativeBesselReal.bessel_real
  apply NativeRealNoise.integralOperator_real (weightedField_measurable L k Λ q q m hm t)
    (fun ω=>weightedSpatial_uniform_bound L (X:=Ω) T hT k hΛ q q t |>.imp fun B hB=>
      ⟨hB.1,fun y p=>hB.2 m ω y p⟩)
    (fun ω y p=>by simp only [weightedField,weightedSpatial,Complex.ofReal_im])
  apply CircleNormalization.push_ae_property _ (fun z : ℂ=>z.im=0)
  exact (realEmbed_ae (V ω)).mono (fun y hy=>by
    change (realEmbed (V ω) y).im=0
    rw [hy]
    exact Complex.ofReal_im _)

theorem meanAverage_real (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (ν : Measure (Fin k→ℝ)) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    {Λ : ℝ} (hΛ : 0≤Λ) (q : ℝ)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2))
    (V : Ω→RealL2) (ω : Ω) :
    ∀ᵐ p : HeatCircle ∂haarAddCircle,(meanAverage L k ν mass ρ hmass hρ Λ q m V ω p).im=0 :=
  NativeBesselReal.integral_real ν _ (fun t=>meanInput_real L T hT k mass ρ hmass hρ hΛ q m hm V t ω)

/-- The complex native field used in the quantitative estimate is
exactly the push-forward of a real physical state with the same norm. -/
theorem meanAverage_realification (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (ν : Measure (Fin k→ℝ)) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    {Λ : ℝ} (hΛ : 0≤Λ) (q : ℝ)
    (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History HeatCircle k=>m z.1 z.2))
    (V : Ω→RealL2) (ω : Ω) :
    let W := meanAverage L k ν mass ρ hmass hρ Λ q m V ω
    embed (NativeBesselReal.part W)=W ∧ ‖NativeBesselReal.part W‖=‖W‖ := by
  intro W
  have hreal := meanAverage_real L T hT k ν mass ρ hmass hρ hΛ q m hm V ω
  exact ⟨NativeBesselReal.embed_part W hreal,NativeBesselReal.part_norm W hreal⟩

end SHE.ActualMeanKernel
