module
public import SHE.ContinuousPicardStepLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.ContinuousPicardIterates
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


structure Paths where
  value:Bool→ℝ≥0→Ω→StateL2
  adapted:∀b,StronglyAdapted 𝓕 (value b)
  continuous:∀b ω,Continuous (fun t=>value b t ω)

def zero:Paths 𝓕 where
  value:=fun _ _ _=>0
  adapted:=fun _ _=>stronglyMeasurable_const
  continuous:=fun _ _=>continuous_const

def next(hz:Continuous z)(p:Paths 𝓕):Paths 𝓕 where
  value:=ContinuousPicardStepLaw.step 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder p.value p.adapted p.continuous I z
  adapted:=ContinuousPicardStepLaw.step_adapted 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder p.value p.adapted p.continuous I B hBDG hpos hnull z
  continuous:=ContinuousPicardStepLaw.step_continuous 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder p.value p.adapted p.continuous I hpos z hz

@[irreducible] def iterate(hz:Continuous z)(n:ℕ):Paths 𝓕:=
  (next 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz)^[n] (zero 𝓕)

@[simp] theorem iterate_zero(hz:Continuous z):
    iterate 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz 0=zero 𝓕:=by
  simp only [iterate,Function.iterate_zero_apply]
@[simp] theorem iterate_succ(hz:Continuous z)(n:ℕ):
    iterate 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz (n+1)=
      next 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz
        (iterate 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz n):=by
  simp only [iterate,Function.iterate_succ_apply']

@[simp] theorem iterate_true(hz:Continuous z)(n:ℕ)(t:ℝ≥0)(ω:Ω):
    (iterate 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz n).value true t ω=0:=by
  cases n with
  | zero=>rw [iterate_zero]; rfl
  | succ n=>rw [iterate_succ]; rfl

end SHE.ContinuousPicardIterates
