module

public import SHE.ControlledDefectActualPacket
public import SHE.ScalarDefectRelativeHaar
public import SHE.StoppedFullDefectSpatial

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.ControlledDefectRootEnergy
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledFamilyProfileForest CoveredControlledLaw
  MeasurableGaussianScores FiniteHaar PhysicalParentGeometry HistoryProductMeasure CommonHaarDefectTrace
  StoppedGaussianScore StoppedAgeBlocks StoppedGaussianFeatures
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

/-- Actual carrier/profile applicability of the full signed spatial
trace. The input scalar is the true full three-Haar point; the only
identity premise is deterministic equality to that displayed point.
All covariance range, moment and parent-forest conditions are derived. -/
theorem energy (hΛ:0<Λ)(k:ℕ):
    let hheat:=Classical.choose (StoppedFullDefectSpatial.energy (1+k))
    let K:=Classical.choose (Classical.choose_spec (StoppedFullDefectSpatial.energy (1+k)))
    let θheat:=Classical.choose (Classical.choose_spec
      (Classical.choose_spec (StoppedFullDefectSpatial.energy (1+k))))
    ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) b)),
      ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
        let z:=separated k ((0:HeatCircle),t,fun _=>0)
        let hx:=fun x:AddCircle (1:ℝ)=>separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
          fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)
        ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal z→
        ∀hp:StrictHistory Zero k z,SmallHistory Zero (uniformHorizon 1) k z→
        (b:ℝ)-(v:ℝ)≤P.horizon→
        ∀(mean:AddCircle (1:ℝ)→WordRecursion.State (1+k)),
        ∀{m W:ℝ}(hm:0<m),0≤W→∀f g0:EllipticField m W,
        let σ:=fun i=>stops Zero k z i-(v:ℝ)
        let target:=fun i=>targets Zero k z i-(v:ℝ)
        let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm
          (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
        let lo:=fun j=>lower Zero k z j-(v:ℝ)
        let hi:=fun j=>upper Zero k z j-(v:ℝ)
        let D:=fun x l=>NativeClippedHaarDirection.column hm f g0 σ target (fun i=>a i+x) (q-(v:ℝ)) Λ l
        let Wr:=fun x=>direction (fun i=>NativeObservationCovariance.row hm g0 (target i) (q-(v:ℝ))
          (nativeCenter (fun i=>a i+x) i))
        let B:=fun x=>GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
          (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
          ((carrier (Base p) k).observations.observations (hx x)) q ((carrier (Base p) k).terminal (hx x)))
          (UncutSmoothWords.test (Base p) k (hx x))) (mean x)
        ∀{g:ℕ}(hg:0<g)(label:Fin (1+k)→Fin g)(rep:Fin g→Fin (1+k))(hrep:∀j,label (rep j)=j)
          (age:Fin (1+k)→ℝ)(hages:∀i,0<age i),(∀i,age i≤hheat)→
          (∀i,target i-(q-(v:ℝ))=4*Real.pi^2*age i)→
        ∀(lower upper M:Fin g→ℝ)(A:ℝ),4*(g:ℝ)^2+1≤A→
          (∀j,0<lower j)→(∀j,lower j≤upper j)→(∀j,1≤M j)→(∀j,upper j≤M j*lower j)→
          (∀i,q-(v:ℝ)+lower (label i)≤σ i)→(∀i,σ i≤q-(v:ℝ)+upper (label i))→
          (∀j l,j<l→A*upper j≤lower l)→
        ∀(width N:Fin g→ℝ),(∀j,0<width j)→(∀j,1≤N j)→
          (∀j i,width j≤groupData label rep age j i)→
          (∀j i,groupData label rep age j i≤N j*width j)→(∀j,θheat*width j≤1)→
        ∀A0 ν:ℝ,0≤A0→0≤ν→
          (∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F (CircleNormalization.scale 1 (2*Real.pi) x)) y‖≤A0*ν^j)→
        let ht:=carrier_orderedTimes Zero (fun _ _=>le_rfl) k z hp
        let G:=sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
          ((timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k z*
            DefectRelativeFactor.total Zero P v k z A0 ν)*
              OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k z) ht
                (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w))
        let ell:=P.lower/8
        let EB:=(g:ℝ)*∑j:Fin g,((max (M j) 8*(lower j)⁻¹)/(ell/2))*(4*W*((1+k:ℕ):ℝ))
        ∀ρ:ℝ,0<ρ→ρ<1/2→
        ∀J:AddCircle (1:ℝ)→ℝ,Measurable J→
          (∀ᵐx∂haarAddCircle,J x=(1/2:ℝ)*(∑'l:HaarNode,(B x (D x l) (Wr x l)+B x (Wr x l) (D x l)+B x (D x l) (D x l))))→
          Integrable (fun x=>|J x|^2) haarAddCircle ∧
            (∫x,|J x|^2 ∂haarAddCircle)≤(9/4:ℝ)*G^2*EB*
              ((g:ℝ)*∑j:Fin g,
                ((max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*K*sqrt (N j)*sqrt (width j)*
                  (signedHeatSqConstant 1 ρ m W*StepInput.negativeEnergy 1 Λ ρ (f.1-g0.1)*
                    (Λ^ρ*(θheat*width j)^(-(1/2:ℝ))+(θheat*width j)^(-(1/2:ℝ)-ρ)))):=by
  intro hheat K θheat
  have hs:=Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (StoppedFullDefectSpatial.energy (1+k))))
  filter_upwards [ControlledDefectActualPacket.packet_sections P hA Λ v b hvb F hF hFm hΛ k] with t ht
  filter_upwards [ht] with w hw
  intro z hx p q hvq hqt hp hsmall hspan mean m W hm hW f g0 σ target a D Wr B
    g hg label rep hrep age hages hageh hage lower upper M A hAsep hlo hlh hM hratio hstlo hsthi hsep
    width N hwidth hN hwlo hwhi hθw A0 ν hA0 hν hjet ht0 G ell EB ρ hρ hρhalf J hJ hJpoint
  let lo:=fun j=>PhysicalChainArrays.lower Zero k z j-(v:ℝ)
  let hi:=fun j=>PhysicalChainArrays.upper Zero k z j-(v:ℝ)
  let cR:UnitAddCircle×ControlledProfile.Domain→ℝ:=fun _=>P.lower/8
  let cC:UnitAddCircle×ControlledProfile.Domain→ℝ:=fun z=>ControlledFixedReserve.coefficient P Λ p.2.1 p.2.2
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2 lo hi)) p.1 z.2
  have hcR:Measurable cR:=measurable_const
  have hold:=fixedProfile_bounds P Λ p.2.1 p.2.2 lo hi (RelativeHistoryGeometry.relative_disjoint Zero k z)
  have hcC:Measurable cC:=
    ((((profile_measurable P Λ p.2.1 p.2.2).comp (measurable_const.prodMk measurable_id))).sub
      (NativeFirstScoreReserve.oldProfile_measurable P (fixedProfile_measurable P Λ p.2.1 p.2.2 lo hi))).comp
        measurable_snd
  have hell:0<ell:=by dsimp [ell];have :=P.lower_pos;positivity
  have hlow:P.lower≤P.upper:=(P.lower_bound 0).trans (P.upper_bound 0)
  have hRb:∀x z,0≤cR (x,z) ∧ cR (x,z)≤P.upper:=by
    intro x z
    exact ⟨hell.le,by change P.lower/8≤P.upper;linarith only [P.lower_pos,hlow]⟩
  have hCb:∀x z,0≤cC (x,z) ∧ cC (x,z)≤P.upper:=by
    intro x z
    have hh:=NativeFirstScoreReserve.residual_bounds P Λ p.2.1 p.2.2 hold p.1 z
    exact ⟨(by have :=P.lower_pos;positivity:0≤3*P.lower/8).trans hh.1,hh.2⟩
  have hRl:∀x z,ell≤cR (x,z):=fun _ _=>le_rfl
  have hCl:∀x z,ell≤cC (x,z):=by
    intro x z
    have hh:=NativeFirstScoreReserve.residual_bounds P Λ p.2.1 p.2.2 hold p.1 z
    dsimp only [ell]
    linarith only [hh.1,P.lower_pos]
  let RR:=fun x=>stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun z=>cR (x,z)) (q-(v:ℝ))
  let CC:=fun x=>stoppedCovariance σ target (nativeCenter (fun i=>a i+x)) (fun z=>cC (x,z)) (q-(v:ℝ))
  let f₁:=fun x=>∑'l,B x (Wr x l) (D x l)
  let f₂:=fun x=>∑'l,B x (D x l) (Wr x l)
  let f₃:=fun x=>2*J x-f₁ x-f₂ x
  have hpacket:∀ᵐx∂haarAddCircle,
      |f₁ x|≤G*(sqrt (∑'l,scoreVariance (RR x) (D x l))*sqrt (∑'l,scoreVariance (CC x) (Wr x l))) ∧
      |f₂ x|≤G*(sqrt (∑'l,scoreVariance (RR x) (Wr x l))*sqrt (∑'l,scoreVariance (CC x) (D x l))) ∧
      |f₃ x|≤G*(sqrt (∑'l,scoreVariance (RR x) (D x l))*sqrt (∑'l,scoreVariance (CC x) (D x l))):=by
    filter_upwards [hw,hJpoint] with x hh hj
    have hpx:StrictHistory Zero k (hx x):=(FixedHistoryTimeFactors.strict_sections Zero (b:ℝ)
      (fun _=>rfl) k t (CircleNormalization.scale 1 (2*Real.pi) x) 0
        (fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x) (fun _=>0)).mpr hp
    have hsx:SmallHistory Zero (uniformHorizon 1) k (hx x):=
      (ScalarRootRelativeGeometry.small_history_sections Zero (b:ℝ) (fun _=>rfl) (b:ℝ)
        (fun _ _=>rfl) (uniformHorizon 1) k t (CircleNormalization.scale 1 (2*Real.pi) x) 0
          (fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x) (fun _=>0)).mpr hsmall
    have hqtx:q<(carrier Zero k).terminal (hx x):=by
      rw [ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl)]
      have hh:q<(carrier Zero k).terminal (separated k ((0:HeatCircle),t,fun _=>0)):=hqt
      rw [ActualMeanKernel.terminal_separated Zero (b:ℝ) (fun _=>rfl)] at hh
      exact hh
    have hpkt:=hh p q hvq hqtx hpx hsx hspan (mean x) hm f g0 A0 ν hA0 hν
      (fun j hj y=>by simpa only [root_separated] using hjet x j hj y)
    have hcov:=ScalarDefectCovarianceGeometry.covariances Zero (b:ℝ) (fun _=>rfl)
      (fun _ _=>⟨rfl,rfl,rfl⟩) P Λ (v:ℝ) q p.1 p.2.1 p.2.2 k t w x
    have hD:=fun l=>ScalarDefectRelativeHaar.clipped Zero (b:ℝ) (fun _=>rfl)
      (fun _ _=>⟨rfl,rfl,rfl⟩) hm f g0 k t w x (v:ℝ) q Λ l
    have hW:=fun l=>ScalarDefectRelativeHaar.current Zero (b:ℝ) (fun _=>rfl)
      (fun _ _=>⟨rfl,rfl,rfl⟩) hm g0 k t w x (v:ℝ) q l
    simp_rw [hD,hW,hcov.1,hcov.2] at hpkt
    rw [(hpkt.2.1.add hpkt.1).tsum_add hpkt.2.2.1,hpkt.2.1.tsum_add hpkt.1] at hj
    have he₃:f₃ x=∑'l,B x (D x l) (D x l):=by dsimp only [f₃,f₁,f₂];linarith only [hj]
    exact ⟨hpkt.2.2.2.1,hpkt.2.2.2.2.1,he₃ ▸ hpkt.2.2.2.2.2⟩
  have hG:0≤G:=by
    apply mul_nonneg (sqrt_nonneg _)
    apply mul_nonneg
    · exact mul_nonneg (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos)
        (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k z hp)
        (TwoFreshBoundedEmptyWord.total_nonneg P _ _ _ A0 ν)
    · exact OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _
  have hageσ:∀i,σ i≤target i:=by
    have hh:=ScalarDefectCovarianceGeometry.covered_stop_eq_target Zero (b:ℝ) (fun _=>rfl)
      (fun _ _=>⟨rfl,rfl,rfl⟩) k z
    intro i
    exact sub_le_sub_right (le_of_eq (congrFun hh i)) _
  have hphys:=hs.2.2.2.2 hg label rep hrep σ target a (q-(v:ℝ)) Λ hΛ age hages hageh
    hage hageσ lower upper M A hAsep hlo hlh hM hratio hstlo hsthi hsep
    width N hwidth hN hwlo hwhi hθw cR cC hcR hcC P.upper ell hRb hCb hell hRl hCl
    hρ hρhalf hm hW f g0 J f₁ f₂ f₃ hJ G hG (fun x=>by dsimp [f₃];ring) hpacket
  exact hphys

end SHE.ControlledDefectRootEnergy
