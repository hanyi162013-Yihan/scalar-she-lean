module

public import SHE.ControlledTerminalPairedFields
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledRelativeScoreForest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.ControlledTerminalPairedFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  ControlledFamilyProfileForest SmoothCylinders UniformSmooth CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledTerminalPairedRelative_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledTerminalPairedRelative_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledTerminalPairedRelative_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable {X:Type} [MeasurableSpace X] (Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (Function.uncurry F))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "SE" => ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TE" => ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "CE" => ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LE" => ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "UE" => ControlledThetaPhysicalGeometry.upper_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

/-- ONE original history event identifies every actual terminal
normalized slot with the genuine relative-age Gaussian product used by
the conditional paired estimates, before ANY random past substitution. -/
theorem relative_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
    ∀p:Inputs,∀newMean oldMean:WordRecursion.State (1+k),
    ∀choices:List (Fin k×Fin (k+1)),∀ν χ:ℝ,∀i:Fin (k+1),
      average P hA Λ v b hvb Z htarget hstop F hF hFm k p h newMean oldMean choices ν χ i=
      PairedAssignedTelescope.averageSlot P Λ p.1 p.2 0 1 0 ((carrier Zero k).terminal h-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        (directions Zero ((carrier Zero k).observations.observations h) k h) choices
        (F (rootParameter k h)) (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i))
        newMean oldMean ν χ i := by
  filter_upwards [ControlledThetaRelativeArrays.full_covariance_relative_fixed_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hres
  intro p newMean oldMean choices ν χ i
  have hv:(v:ℝ)≤(carrier Zero k).terminal h:=(carrier Zero k).terminal_base h
  have ht0:0≤(carrier Zero k).terminal h:=v.2.trans hv
  have hm:=ControlledThetaRelativeWord.old_covariance_relative P hA Λ v b hvb Z htarget hstop F hF hFm
    (0,p) k h hv (by rw [TME (0,p) (0,(0,0)) k h])
  rw [SE (0,p) (0,(0,0)) k h,TE (0,p) (0,(0,0)) k h,CE (0,p) (0,(0,0)) k h,
    LE (0,p) (0,(0,0)) k h,UE (0,p) (0,(0,0)) k h] at hm
  have hd:directions (Base (0,p)) ((carrier (Base (0,p)) k).observations.observations h) k h=
      directions Zero ((carrier Zero k).observations.observations h) k h:=by
    rw [OME (0,p) (0,(0,0)) k h]
    exact ControlledThetaPhysicalGeometry.directions_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
      (0,p) (0,(0,0)) _ k h
  have hB:=hres (0,p) ((carrier Zero k).terminal h) ht0 le_rfl
  have hbas(η:ℝ):baseline (Base (η,p)) k h=
      (fun j=>profile P Λ p.1 p.2 (η,(targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers Zero k h (leafIndex k (fun i=>i) j)))):=by
    funext j
    have hb:=ControlledThetaRelativeWord.baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm
      (η,p) k h j
    rw [TE (η,p) (0,(0,0)) k h,CE (η,p) (0,(0,0)) k h] at hb
    exact hb
  dsimp only [average,PairedAssignedTelescope.averageSlot]
  rw [TME (0,p) (0,(0,0)) k h,hm,hd,hB,hbas 1,hbas 0]

end SHE.ControlledTerminalPairedFields
