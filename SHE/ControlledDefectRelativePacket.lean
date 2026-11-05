module

public import SHE.ControlledThetaDefectEnvelope
public import SHE.DefectHistorySections
public import SHE.DefectRelativeFactor
public import SHE.ControlledScalarReference

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.ControlledDefectRelativePacket
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledFamilyProfileForest CoveredControlledLaw
  MeasurableGaussianScores FiniteHaar PhysicalParentGeometry HistoryProductMeasure
open scoped NNReal BigOperators
local instance controlledDefectRelativePacket_period:Fact (0<2*π):=⟨by positivity⟩
local instance controlledDefectRelativePacket_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance controlledDefectRelativePacket_sigma:MeasurableSpace CircleL2:=borel _
local instance controlledDefectRelativePacket_borel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Z"=>ControlledScalarReference.observations b
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z
  (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
local notation "Zero"=>Base (0,(0,0))

/-- The actual scalar full-word Hessian on ONE old-time/relative-space
event, with every interpolation value, past state and current mean
inside the root section. Its whole positive old envelope factors into
the exact time budget and the true earlier-parent density. -/
theorem packet_sections (k:ℕ):
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) b)),
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
        ∀ᵐx:AddCircle (1:ℝ)∂haarAddCircle,
          let h:=separated k (CircleNormalization.scale 1 (2*π) x,t,
            fun i=>w i+CircleNormalization.scale 1 (2*π) x)
          let z:=separated k ((0:HeatCircle),t,fun _=>0)
          ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→
          ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon 1) k h→
          (b:ℝ)-(v:ℝ)≤P.horizon→
          ∀(mean:WordRecursion.State (1+k))(E V:HaarNode→WordRecursion.State (1+k)),
          let σ:=fun i=>stops Zero k h i-(v:ℝ)
          let target:=fun i=>targets Zero k h i-(v:ℝ)
          let center:=centers Zero k h
          let lo:=fun j=>lower Zero k h j-(v:ℝ)
          let hi:=fun j=>upper Zero k h j-(v:ℝ)
          let R:=NativeFirstScoreReserve.covariance P σ target center (q-(v:ℝ))
          let C:=ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
            (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2 lo hi))
            σ target center (q-(v:ℝ)) p.1
          (∀j,E j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)→
          (∀j,V j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)→
          Summable (fun j=>scoreVariance R (E j))→Summable (fun j=>scoreVariance C (V j))→
          ∀A0 ν:ℝ,0≤A0→0≤ν→
          (∀j,j≤k→∀y,‖iteratedFDeriv ℝ j (F (rootParameter k h)) y‖≤A0*ν^j)→
          let ht:=carrier_orderedTimes Zero (fun _ _=>le_rfl) k h hp
          let ht0:OrderedHeatForests.OrderedTimes k (targets Zero k z):=by
            have he:=FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) (fun _=>rfl)
              (fun _=>b) (fun _ _=>rfl) k t (CircleNormalization.scale 1 (2*π) x) 0
                (fun i=>w i+CircleNormalization.scale 1 (2*π) x) (fun _=>0)
            change OrderedHeatForests.OrderedTimes k (targets Zero k
              (separated k (CircleNormalization.scale 1 (2*π) x,t,
                fun i=>w i+CircleNormalization.scale 1 (2*π) x))) at ht
            simpa only [he] using ht
          let G:=(timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k z*
            DefectRelativeFactor.total Zero P v k z A0 ν)*
              OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k z) ht0
                (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w)
          let B:=GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
            (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
            ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
            (UncutSmoothWords.test (Base p) k h)) mean
          Summable (fun j=>B (V j) (E j)) ∧
            |∑'j,B (V j) (E j)|≤sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*G*
              (sqrt (∑'j,scoreVariance R (E j))*sqrt (∑'j,scoreVariance C (V j))):=by
  have h:=DefectHistorySections.unit_common_event
    (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) k
      (ControlledThetaDefectEnvelope.hessian_envelope_all_parameters_ae
        P hA Λ v b hvb Z (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
          (fun _ _=>le_rfl) haarAddCircle k)
  filter_upwards [h] with t ht
  filter_upwards [ht] with w hw
  filter_upwards [hw] with x hx
  intro h z p q hvq hqt hp hsmall hspan mean E V σ target center lo hi R C hE hV hsE hsV
    A0 ν hA0 hν hjet ht0 G B
  let ht:=carrier_orderedTimes Zero (fun _ _=>le_rfl) k h hp
  have hh:=hx p q hvq hqt hp hsmall hspan mean E V hE hV hsE hsV A0 ν hA0 hν hjet
  have he:
      (timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h) ht (centers Zero k h))*
          TwoFreshBoundedEmptyWord.total (d:=1) P lo hi
            (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν=G:=by
    rw [DefectRelativeFactor.total_actual Zero P (v:ℝ) k h]
    exact DefectRelativeFactor.factor_relative Zero (b:ℝ) (fun _=>rfl) P v
      (fraction P*P.lower) b (uniformConstant 1) (fun _ _=>rfl) (fun _ _=>rfl)
      k t (CircleNormalization.scale 1 (2*π) x) w ht A0 ν
  change Summable (fun j=>B (V j) (E j)) ∧
    |∑'j,B (V j) (E j)|≤sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
      ((timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h) ht (centers Zero k h))*
          TwoFreshBoundedEmptyWord.total (d:=1) P lo hi
            (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν)*
      (sqrt (∑'j,scoreVariance R (E j))*sqrt (∑'j,scoreVariance C (V j))) at hh
  rw [he] at hh
  exact hh

end SHE.ControlledDefectRelativePacket
