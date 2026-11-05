module

public import SHE.ControlledDefectRelativePacket
public import SHE.ControlledDefectFreshRanges

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.ControlledDefectActualPacket
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledFamilyProfileForest CoveredControlledLaw
  MeasurableGaussianScores FiniteHaar PhysicalParentGeometry HistoryProductMeasure CommonHaarDefectTrace
open scoped NNReal BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Z"=>ControlledScalarReference.observations b
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z
  (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero"=>Base (0,(0,0))

/-- All THREE true full-Haar Hessian packets of the actual recursive
word, with every fresh range and score summability condition proved.
The common old history event precedes all current means/past inputs. -/
theorem packet_sections (hΛ:0<Λ)(k:ℕ):
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) b)),
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
        ∀ᵐx:AddCircle (1:ℝ)∂haarAddCircle,
          let h:=separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
            fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)
          let z:=separated k ((0:HeatCircle),t,fun _=>0)
          ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→
          ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon 1) k h→
          (b:ℝ)-(v:ℝ)≤P.horizon→
          ∀(mean:WordRecursion.State (1+k)),
          ∀{m W:ℝ}(hm:0<m)(f g:EllipticField m W),
          let σ:=fun i=>stops Zero k h i-(v:ℝ)
          let target:=fun i=>targets Zero k h i-(v:ℝ)
          let center:=centers Zero k h
          let lo:=fun j=>lower Zero k h j-(v:ℝ)
          let hi:=fun j=>upper Zero k h j-(v:ℝ)
          let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm (center i)
          let R:=NativeFirstScoreReserve.covariance P σ target center (q-(v:ℝ))
          let C:=ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
            (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2 lo hi))
            σ target center (q-(v:ℝ)) p.1
          let D:=NativeClippedHaarDirection.column hm f g σ target a (q-(v:ℝ)) Λ
          let Wr:=direction (fun i=>NativeObservationCovariance.row hm g (target i) (q-(v:ℝ)) (center i))
          ∀A0 ν:ℝ,0≤A0→0≤ν→
          (∀j,j≤k→∀y,‖iteratedFDeriv ℝ j (F (rootParameter k h)) y‖≤A0*ν^j)→
          let ht:=carrier_orderedTimes Zero (fun _ _=>le_rfl) k h hp
          let ht0:OrderedHeatForests.OrderedTimes k (targets Zero k z):=by
            have he:=FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) (fun _=>rfl)
              (fun _=>b) (fun _ _=>rfl) k t (CircleNormalization.scale 1 (2*Real.pi) x) 0
                (fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x) (fun _=>0)
            change OrderedHeatForests.OrderedTimes k (targets Zero k
              (separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
                fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x))) at ht
            simpa only [he] using ht
          let G:=sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
            ((timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k z*
              DefectRelativeFactor.total Zero P v k z A0 ν)*
                OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k z) ht0
                  (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w))
          let B:=GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
            (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
            ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
            (UncutSmoothWords.test (Base p) k h)) mean
          Summable (fun l=>B (Wr l) (D l)) ∧ Summable (fun l=>B (D l) (Wr l)) ∧
            Summable (fun l=>B (D l) (D l)) ∧
            |∑'l,B (Wr l) (D l)|≤G*(sqrt (∑'l,scoreVariance R (D l))*sqrt (∑'l,scoreVariance C (Wr l))) ∧
            |∑'l,B (D l) (Wr l)|≤G*(sqrt (∑'l,scoreVariance R (Wr l))*sqrt (∑'l,scoreVariance C (D l))) ∧
            |∑'l,B (D l) (D l)|≤G*(sqrt (∑'l,scoreVariance R (D l))*sqrt (∑'l,scoreVariance C (D l))):=by
  have he:=ControlledDefectRelativePacket.packet_sections P hA Λ v b hvb F hF hFm k
  filter_upwards [he] with t ht
  filter_upwards [ht] with w hw
  filter_upwards [hw] with x hx
  intro h z p q hvq hqt hp hsmall hspan mean m W hm f g σ target center lo hi a R C D Wr
    A0 ν hA0 hν hjet ht0 G B
  have hr:=ControlledDefectFreshRanges.ranges Zero (b:ℝ) (fun _=>rfl)
    (fun _ _=>⟨rfl,rfl,rfl⟩) P Λ hΛ p k h q hvq hqt hm f g
  have h₁:=hx p q hvq hqt hp hsmall hspan mean D Wr hr.1 hr.2.2.2.2.2.2.1
    hr.2.1 hr.2.2.2.2.2.2.2 A0 ν hA0 hν hjet
  have h₂:=hx p q hvq hqt hp hsmall hspan mean Wr D hr.2.2.1 hr.2.2.2.2.1
    hr.2.2.2.1 hr.2.2.2.2.2.1 A0 ν hA0 hν hjet
  have h₃:=hx p q hvq hqt hp hsmall hspan mean D D hr.1 hr.2.2.2.2.1
    hr.2.1 hr.2.2.2.2.2.1 A0 ν hA0 hν hjet
  exact ⟨h₁.1,h₂.1,h₃.1,h₁.2,h₂.2,h₃.2⟩

end SHE.ControlledDefectActualPacket
