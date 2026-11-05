module

public import SHE.ControlledDefectRootEnergy
public import SHE.StoppedFullDefectCost
public import SHE.NativeAgePartitionFrame
public import SHE.AgeBlockPairSum

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.ControlledDefectAgeRMS
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

/-- Actual full-word root RMS at arbitrary original ages. The
dimension-only heat horizon and coefficient are fixed BEFORE control
strength, past/current states, all histories and root frequency. -/
theorem rms (ellP:ℝ)(hellP:0<ellP)
    {m W:ℝ}(hm:0<m)(hW:0≤W){ρ:ℝ}(hρ:0<ρ)(hρhalf:ρ<1/2)(k:ℕ):
    ∃H C:ℝ,0<H ∧ 0<C ∧
      ∀(P:CanonicalCovariance.ProfileParameters),P.lower=ellP→
      ∀hSmooth:BoundedSmooth P.coefficient,∀Λ:ℝ,1≤Λ→
      ∀(v b:ℝ≥0)(hvb:v≤b)(F:HeatCircle→WordRecursion.State 1→ℝ)
        (hF:UniformBoundedSmooth F)(hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2)),
      let Z:=ControlledScalarReference.observations b
      let Base:=ControlledReferenceThetaGeometry.level P P.coefficient hSmooth Λ v b hvb Z
        (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm
      let Zero:=Base (0,(0,0))
      ∀ᵐt:Fin k→ℝ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) b)),
        ∀ᵐw:Fin k→HeatCircle∂Measure.pi (fun _=>haarAddCircle),
          let z:=separated k ((0:HeatCircle),t,fun _=>0)
          let hx:=fun x:AddCircle (1:ℝ)=>separated k (CircleNormalization.scale 1 (2*Real.pi) x,t,
            fun i=>w i+CircleNormalization.scale 1 (2*Real.pi) x)
          ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal z→
          ∀hp:StrictHistory Zero k z,SmallHistory Zero (uniformHorizon 1) k z→
          (b:ℝ)-(v:ℝ)≤P.horizon→(b:ℝ)-(v:ℝ)≤H→
          ∀(mean:AddCircle (1:ℝ)→WordRecursion.State (1+k))(f g0:EllipticField m W),
          let σ:=fun i=>stops Zero k z i-(v:ℝ)
          let target:=fun i=>targets Zero k z i-(v:ℝ)
          let a:=fun i=>(CircleNormalization.scale 1 (2*Real.pi)).symm
            (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
          let D:=fun x l=>NativeClippedHaarDirection.column hm f g0 σ target (fun i=>a i+x) (q-(v:ℝ)) Λ l
          let Wr:=fun x=>direction (fun i=>NativeObservationCovariance.row hm g0 (target i) (q-(v:ℝ))
            (nativeCenter (fun i=>a i+x) i))
          let B:=fun x=>GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
            (referenceData P P.coefficient hSmooth Λ p.1 v b hvb p.2).reference
            ((carrier (Base p) k).observations.observations (hx x)) q ((carrier (Base p) k).terminal (hx x)))
            (UncutSmoothWords.test (Base p) k (hx x))) (mean x)
          ∀A0 ν:ℝ,0≤A0→0≤ν→
            (∀x j,j≤k→∀y,‖iteratedFDeriv ℝ j (F (CircleNormalization.scale 1 (2*Real.pi) x)) y‖≤A0*ν^j)→
          let ht:=carrier_orderedTimes Zero (fun _ _=>le_rfl) k z hp
          let G:=sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
            ((timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k z*
              DefectRelativeFactor.total Zero P v k z A0 ν)*
                OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k z) ht
                  (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w))
          ∀J:AddCircle (1:ℝ)→ℝ,Measurable J→
            (∀ᵐx∂haarAddCircle,J x=(1/2:ℝ)*(∑'l:HaarNode,(B x (D x l) (Wr x l)+B x (Wr x l) (D x l)+B x (D x l) (D x l))))→
            Integrable (fun x=>|J x|^2) haarAddCircle ∧
              Λ^(-ρ/2)*sqrt (∫x,|J x|^2 ∂haarAddCircle)≤C*G*
                sqrt (StepInput.negativeEnergy 1 Λ ρ (f.1-g0.1))*
                  (∑i:Fin (1+k),∑j:Fin (1+k),DefectCombinedTime.kernel Λ ρ
                    (targets Zero k z i-(carrier Zero k).terminal z)
                    (targets Zero k z j-(carrier Zero k).terminal z) ((carrier Zero k).terminal z-q)):=by
  classical
  let n:=1+k
  let hheat:=Classical.choose (StoppedFullDefectSpatial.energy n)
  let K:=Classical.choose (Classical.choose_spec (StoppedFullDefectSpatial.energy n))
  let θ:=Classical.choose (Classical.choose_spec (Classical.choose_spec (StoppedFullDefectSpatial.energy n)))
  have hs:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (StoppedFullDefectSpatial.energy n)))
  let clock:=4*Real.pi^2
  have hclock:0<clock:=by dsimp [clock];positivity
  let H:=min (clock*hheat) (clock/θ)
  have hH:0<H:=lt_min (mul_pos hclock hs.1) (div_pos hclock hs.2.2.2.1)
  let A:ℝ:=4*(n:ℝ)^2+1
  have hA:1≤A:=by dsimp [A];nlinarith only [sq_nonneg (n:ℝ)]
  let M:=A^n
  have hM:1≤M:=one_le_pow₀ hA
  have hell:0<ellP/8:=by positivity
  have hSigned:0≤signedHeatSqConstant 1 ρ m W:=signedHeatSqConstant_nonneg zero_le_one hρ hρhalf hW
  obtain ⟨C,hC,hcost0⟩:=StoppedFullDefectCost.cost K θ (ellP/8) W M
    (signedHeatSqConstant 1 ρ m W) ρ hs.2.2.1.le hs.2.2.2.1 hell hW hM hSigned n
  refine ⟨H,C,hH,hC,?_⟩
  intro P hLower hSmooth Λ hΛ v b hvb F hF hFm Z Base Zero
  have hcost:=@hcost0
  rw [←hLower] at hcost
  have hΛp:0<Λ:=zero_lt_one.trans_le hΛ
  have hr:=ControlledDefectRootEnergy.energy P hSmooth Λ v b hvb F hF hFm hΛp k
  filter_upwards [hr] with t ht
  filter_upwards [ht] with w hw
  intro z hx p q hvq hqt hp hsmall hspan hspanH mean f g0 σ target a D Wr B A0 ν hA0 hν hjet ht0 G J hJ hpoint
  let d:=fun i:Fin (1+k)=>target i-(q-(v:ℝ))
  have hσ:σ=target:=by
    funext i
    exact congrArg (fun s:ℝ=>s-(v:ℝ))
      (congrFun (ScalarDefectCovarianceGeometry.covered_stop_eq_target Zero (b:ℝ)
        (fun _=>rfl) (fun _ _=>⟨rfl,rfl,rfl⟩) k z) i)
  have hd:∀i,0<d i:=by
    intro i
    have hh:=(carrier Zero k).targets_after z i
    change (carrier Zero k).terminal z≤targets Zero k z i at hh
    change 0<(targets Zero k z i-(v:ℝ))-(q-(v:ℝ))
    linarith only [hqt,hh]
  have hdH:∀i,d i≤H:=by
    intro i
    have hh:=RelativeHistoryGeometry.carrier_age_le_span Zero (b:ℝ) (fun _=>le_rfl)
      (fun _ _=>le_rfl) k z hvq i
    change targets Zero k z i-q≤(b:ℝ)-(v:ℝ) at hh
    have hh':d i=targets Zero k z i-q:=by dsimp only [d,target];ring
    rw [hh']
    exact hh.trans hspanH
  obtain ⟨Q⟩:=AgeClustering.exists_partition d hd hA
  have hg:=Q.count_pos (by omega:0<1+k)
  have hQA:4*(Q.count:ℝ)^2+1≤A:=by
    have hc:(Q.count:ℝ)≤(n:ℝ):=by exact_mod_cast Q.count_le
    dsimp only [A]
    nlinarith only [hc,show (0:ℝ)≤(Q.count:ℝ) by positivity,show (0:ℝ)≤(n:ℝ) by positivity]
  let age:=NativeAgePartitionFrame.time (d:=d)
  let width:=NativeAgePartitionFrame.width Q
  have hage:∀i,0<age i:=fun i=>div_pos (hd i) hclock
  have hageh:∀i,age i≤hheat:=by
    intro i
    apply (div_le_iff₀ hclock).mpr
    have hi: d i≤clock*hheat:=(hdH i).trans (min_le_left _ _)
    simpa only [mul_comm] using hi
  have hclockage:∀i,target i-(q-(v:ℝ))=4*Real.pi^2*age i:=by
    intro i
    change d i=clock*(d i/clock)
    rw [mul_div_cancel₀ _ hclock.ne']
  have hlo:∀i,q-(v:ℝ)+Q.lower (Q.label i)≤σ i:=by
    intro i
    rw [hσ]
    have hh:=Q.lower_bound i
    dsimp only [d] at hh
    linarith only [hh]
  have hhi:∀i,σ i≤q-(v:ℝ)+Q.upper (Q.label i):=by
    intro i
    rw [hσ]
    have hh:=Q.upper_bound i
    dsimp only [d] at hh
    linarith only [hh]
  have hθH:θ*H≤clock:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_right (clock*hheat) (clock/θ)) hs.2.2.2.1.le
    apply hh.trans_eq
    change θ*(clock/θ)=clock
    field_simp [show θ≠0 from hs.2.2.2.1.ne']
  have hwi:=fun j i=>NativeAgePartitionFrame.group_bounds Q j i
  have hbound:=hw p q hvq hqt hp hsmall hspan mean hm hW f g0 hg Q.label Q.rep Q.label_rep
    age hage hageh hclockage Q.lower Q.upper (fun _=>M) A hQA Q.lower_pos Q.lower_le_upper
    (fun _=>hM) Q.ratio hlo hhi Q.separation width (fun _=>M)
    (NativeAgePartitionFrame.width_pos Q) (fun _=>hM) (fun j i=>(hwi j i).1)
    (fun j i=>(hwi j i).2) (NativeAgePartitionFrame.scaled_width Q hs.2.2.2.1.le hdH hθH)
    A0 ν hA0 hν hjet ρ hρ hρhalf J hJ hpoint
  have hG:0≤G:=by
    apply mul_nonneg (sqrt_nonneg _)
    apply mul_nonneg
    · exact mul_nonneg (timeWeight_nonneg Zero (mul_pos (fraction_pos P) P.lower_pos)
        (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k z hp)
        (TwoFreshBoundedEmptyWord.total_nonneg P _ _ _ A0 ν)
    · exact OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _
  let E:=StepInput.negativeEnergy 1 Λ ρ (f.1-g0.1)
  have hE:0≤E:=FiniteHaar.negativeEnergy_nonneg 1 ρ hΛp.le _
  let X:=fun i:Fin Q.count=>((max M 8*min 1 (Λ*Q.lower i)^2/Q.lower i)/((P.lower/8)/2))*
    K*sqrt M*sqrt (Q.lower i/(4*Real.pi^2))*signedHeatSqConstant 1 ρ m W*
      (Λ^ρ*(θ*(Q.lower i/(4*Real.pi^2)))^(-(1/2:ℝ))+
        (θ*(Q.lower i/(4*Real.pi^2)))^(-(1/2:ℝ)-ρ))
  let Y:=fun i:Fin Q.count=>(max M 8/Q.lower i)/((P.lower/8)/2)*(4*W*(n:ℝ))
  have hEB:(Q.count:ℝ)*(∑i:Fin Q.count,((max M 8*(Q.lower i)⁻¹)/((P.lower/8)/2))*(4*W*(n:ℝ)))=
      (Q.count:ℝ)*∑i:Fin Q.count,Y i:=by
    simp only [Y,div_eq_mul_inv]
  have hEA:(Q.count:ℝ)*(∑i:Fin Q.count,
      ((max M 8*min 1 (Λ*Q.lower i)^2*(Q.lower i)⁻¹)/((P.lower/8)/2))*K*sqrt M*sqrt (width i)*
        (signedHeatSqConstant 1 ρ m W*E*
          (Λ^ρ*(θ*width i)^(-(1/2:ℝ))+(θ*width i)^(-(1/2:ℝ)-ρ))))=
      (Q.count:ℝ)*(∑i:Fin Q.count,X i)*E:=by
    rw [mul_assoc,Finset.sum_mul]
    apply congrArg (fun y:ℝ=>(Q.count:ℝ)*y)
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [X,width,NativeAgePartitionFrame.width]
    simp only [div_eq_mul_inv]
    ring
  have hI:(∫x,|J x|^2 ∂haarAddCircle)≤
      (9/4:ℝ)*G^2*((Q.count:ℝ)*∑j:Fin Q.count,Y j)*((Q.count:ℝ)*(∑i:Fin Q.count,X i)*E):=by
    convert hbound.2 using 1
    rw [hEA,hEB]
  have hnum:=hcost (g:=Q.count) Q.count_le Λ hΛ Q.lower Q.lower_pos G E hG hE
  have hS:=mul_le_mul_of_nonneg_left (sqrt_le_sqrt hI) (rpow_nonneg hΛp.le (-ρ/2))
  have hsCost:Λ^(-ρ/2)*sqrt (∫x,|J x|^2 ∂haarAddCircle)≤
      C*G*sqrt E*(∑i:Fin Q.count,∑j:Fin Q.count,
        min 1 (Λ*Q.lower i)*(Q.lower i)^(-(1/2:ℝ))*(Q.lower j)^(-(1/2:ℝ))*
          (1+Λ^(-ρ/2)*(Q.lower i)^(-ρ/2))):=hS.trans hnum
  let offset:=fun i:Fin (1+k)=>targets Zero k z i-(carrier Zero k).terminal z
  let τ:=(carrier Zero k).terminal z-q
  have ho:∀i,0≤offset i:=fun i=>sub_nonneg.mpr ((carrier Zero k).targets_after z i)
  have hτ:0≤τ:=(sub_pos.mpr hqt).le
  have hsum:(∑i:Fin Q.count,∑j:Fin Q.count,
      min 1 (Λ*Q.lower i)*(Q.lower i)^(-(1/2:ℝ))*(Q.lower j)^(-(1/2:ℝ))*
        (1+Λ^(-ρ/2)*(Q.lower i)^(-ρ/2)))≤
      ∑i:Fin (1+k),∑j:Fin (1+k),DefectCombinedTime.kernel Λ ρ (offset i) (offset j) τ:=by
    have he(i j:Fin Q.count):
        min 1 (Λ*Q.lower i)*(Q.lower i)^(-(1/2:ℝ))*(Q.lower j)^(-(1/2:ℝ))*
          (1+Λ^(-ρ/2)*(Q.lower i)^(-ρ/2))=
        DefectCombinedTime.kernel Λ ρ (offset (Q.rep i)) (offset (Q.rep j)) τ:=by
      have hi:τ+offset (Q.rep i)=Q.lower i:=by rw [Q.lower_eq_rep];dsimp [τ,offset,d,target];ring
      have hj:τ+offset (Q.rep j)=Q.lower j:=by rw [Q.lower_eq_rep];dsimp [τ,offset,d,target];ring
      have hh:=NativeAgePartitionFrame.kernel_factorization Λ ρ (offset (Q.rep i)) (offset (Q.rep j)) τ
        (by rw [hi];exact Q.lower_pos i)
      rw [hi,hj] at hh
      exact hh.symm
    simp_rw [he]
    exact AgeBlockPairSum.pairs Q _ (fun i j=>DefectCombinedTime.nonneg hΛp.le (ho i) (ho j) hτ)
  exact ⟨hbound.1,hsCost.trans (mul_le_mul_of_nonneg_left hsum (by positivity))⟩

end SHE.ControlledDefectAgeRMS
