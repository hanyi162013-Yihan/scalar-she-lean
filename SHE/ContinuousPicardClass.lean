module
public import SHE.ContinuousPicardIterationData
public import SHE.ContinuousNonlinearClass
public import SHE.FixedHorizonPicardIterates
public import SHE.DampedConvolutionZero
public import SHE.PredictableProcessLimit
public import SHE.ContinuousPicardStepLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.ContinuousPicardClass
open MeasureTheory Set Filter PredictableL2 LowBands
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hH:(H:ℝ)≤1)
variable(a:Bool→ℝ→ℝ)(ha:∀b,Measurable (a b))(ell M Holder:Bool→ℝ)
variable(hell:∀b,0<ell b)(hb:∀b z,ell b≤a b z∧a b z≤M b)
variable(β:ℝ)(hβ:0<β)(hHolder:∀b,0≤Holder b)
variable(hholder:∀b z w,|a b z-a b w|≤Holder b*|z-w|^β)
variable(U:Bool→ℝ≥0→Ω→StateL2)(hUa:∀b,StronglyAdapted 𝓕 (U b))
variable(hc:∀b ω,Continuous (fun t=>U b t ω))
variable(L:Bool→ℝ≥0)(hLip:∀b,LipschitzWith (L b) (fun z=>(a b z:ℂ)))
abbrev Source:=(Bool→ℝ≥0→StateL2)×(Bool→FiniteHaar.HaarNode→ℝ≥0→ℝ)
abbrev Tag:=Sum (Bool×ℝ≥0) (Bool×FiniteHaar.HaarNode×ℝ≥0)
abbrev JointState:=StateL2×ℝ

variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable(J:Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)

variable (B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable (hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)


variable (z:ℝ≥0→StateL2)



local notation "N"=>NonlinearConvolution.map 𝓕 μ H (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false)
local notation "Add"=>NonlinearConvolution.map 𝓕 μ H (ha true) (hell true) (hb true) hβ (hHolder true) (hholder true) (I true) (0:Process (E:=StateL2) 𝓕 μ H)

def process(Z:Process (E:=StateL2) 𝓕 μ H)(n:ℕ):Process (E:=StateL2) 𝓕 μ H:=
  (fun w=>Z+Add+N w)^[n] 0
local notation "ProcessN"=>process 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I
variable (hz:Continuous z)
local notation "PathN"=>ContinuousPicardIterates.iterate
  𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz

/-- The literal continuous Picard paths represent the original
predictable-L2 Picard iterates on the common full horizon. -/
theorem class_ae(Z:Process (E:=StateL2) 𝓕 μ H)
    (hZ:(fun p:ℝ≥0×Ω=>z p.1)=ᵐ[energyMeasure μ H] Z):
    ∀n:ℕ,(fun p:ℝ≥0×Ω=>(PathN n).value false p.1 p.2)=ᵐ[energyMeasure μ H] ProcessN Z n:=by
  have hzero:(fun _:ℝ≥0×Ω=>(0:StateL2))=ᵐ[energyMeasure μ H] (0:Process (E:=StateL2) 𝓕 μ H):=
    (ae_eq_of_ae_eq_trim (Lp.coeFn_zero StateL2 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))).symm
  intro n
  induction n with
  | zero=>simpa only [ContinuousPicardIterates.iterate_zero,ContinuousPicardIterates.zero,
      process,Function.iterate_zero_apply] using hzero
  | succ n ih=>
    let p:=PathN n
    let C:Bool→ℝ≥0×Ω→StateL2:=fun b q=>TwoChannelContinuousLaw.convolution
      𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder p.value p.adapted p.continuous I b q.1 q.2
    have htrue:(fun q:ℝ≥0×Ω=>p.value true q.1 q.2)=ᵐ[energyMeasure μ H] (0:Process (E:=StateL2) 𝓕 μ H):=by
      simpa only [p,ContinuousPicardIterates.iterate_true] using hzero
    have hc0:C true=ᵐ[energyMeasure μ H] Add:=ContinuousNonlinearClass.version_ae
      𝓕 μ H hH (ha true) (hell true) (hb true) hβ (hHolder true) (hholder true)
      (p.value true) (p.adapted true) (p.continuous true) (I true) (B true) (hBDG true) hpos 0 htrue
    have hc1:C false=ᵐ[energyMeasure μ H] N (ProcessN Z n):=ContinuousNonlinearClass.version_ae
      𝓕 μ H hH (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false)
      (p.value false) (p.adapted false) (p.continuous false) (I false) (B false) (hBDG false) hpos (ProcessN Z n) ih
    have hstep:(fun q:ℝ≥0×Ω=>(PathN (n+1)).value false q.1 q.2)=
        (fun q=>z q.1+C true q+C false q):=by
      rw [ContinuousPicardIterates.iterate_succ]
      rfl
    have hp:ProcessN Z (n+1)=Z+Add+N (ProcessN Z n):=by
      exact Function.iterate_succ_apply' (fun w=>Z+Add+N w) n 0
    rw [hstep,hp]
    filter_upwards [hZ,hc0,hc1,
      ae_eq_of_ae_eq_trim (Lp.coeFn_add Z Add),
      ae_eq_of_ae_eq_trim (Lp.coeFn_add (Z+Add) (N (ProcessN Z n)))] with q hzq h0 h1 ha0 ha1
    simp only [Pi.add_apply] at ha0 ha1
    rw [ha1,ha0,hzq,h0,h1]

/-- The continuous representatives converge in genuine unweighted
physical product energy to any supplied smooth mild fixed-point version. -/
theorem energy_limit {LF:ℝ≥0}(hLipF:LipschitzWith LF (fun x=>(a false x:ℂ)))
    (Z v:Process (E:=StateL2) 𝓕 μ H)
    (hZ:(fun p:ℝ≥0×Ω=>z p.1)=ᵐ[energyMeasure μ H] Z)
    (hv:v=Z+Add+N v)(V:ℝ≥0→Ω→StateL2)
    (hV:Function.uncurry V=ᵐ[energyMeasure μ H] v):
    (∀n,Integrable (fun q:ℝ≥0×Ω=>‖(PathN n).value false q.1 q.2-V q.1 q.2‖^2) (energyMeasure μ H)) ∧
    Tendsto (fun n=>∫q:ℝ≥0×Ω,‖(PathN n).value false q.1 q.2-V q.1 q.2‖^2 ∂energyMeasure μ H)
      atTop (𝓝 0):=by
  have he:DampedNonlinearConvolution.map 𝓕 μ H hH (Λ:=0) (by norm_num)
      (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false)=N:=
    funext (DampedConvolutionZero.nonlinear 𝓕 μ H (hell false) (ha false) (hb false)
      hβ (hHolder false) (hholder false) hH (I false))
  have hveq:v=(Z+Add)+DampedNonlinearConvolution.map 𝓕 μ H hH (Λ:=0) (by norm_num)
      (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false) v:=by
    rw [he]
    exact hv
  have ht:=FixedHorizonPicardIterates.tendsto 𝓕 μ H hH (Λ:=0) (by norm_num)
    (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false)
    (B false) (hBDG false) hpos hLipF (Z+Add) v 0 hveq
  rw [he] at ht
  exact PredictableProcessLimit.versions 𝓕 μ H (ProcessN Z) v
    (fun n q=>(PathN n).value false q.1 q.2) (Function.uncurry V)
    (class_ae 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz Z hZ) hV ht

end SHE.ContinuousPicardClass
