module
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselFiniteIdentity
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P I:Type*}[MeasurableSpace P]

/-- Genuine spatial L2 representatives respect finite scalar identities
before and after the native Bessel multiplier. No stochastic identity
is inferred from a scalar algebraic identity by this lemma. -/
theorem finite_sum (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(s:Finset I)
    (F:P×HeatCircle→ℂ)(hF:Measurable F)(G:I→P×HeatCircle→ℂ)(hG:∀i,Measurable (G i))
    (p:P)(hp:MemLp (fun x=>F (p,x)) 2 haarAddCircle)
    (hGp:∀i∈s,MemLp (fun x=>G i (p,x)) 2 haarAddCircle)
    (he:∀ᵐx∂haarAddCircle,F (p,x)=∑i∈s,G i (p,x)):
    NativeBesselFieldAE.value Λ ρ hΛ hρ F p=
      ∑i∈s,NativeBesselFieldAE.value Λ ρ hΛ hρ (G i) p:=by
  let A:=MeasurableL2FieldAE.realization haarAddCircle F p
  let B:=fun i=>MeasurableL2FieldAE.realization haarAddCircle (G i) p
  have ha:A=ᵐ[haarAddCircle] fun x=>F (p,x):=
    MeasurableL2FieldAE.realization_ae haarAddCircle F hF p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle F hF p).mp hp)
  have hb:∀i∈s,B i=ᵐ[haarAddCircle] fun x=>G i (p,x):=by
    intro i hi
    exact MeasurableL2FieldAE.realization_ae haarAddCircle (G i) (hG i) p
      ((MeasurableL2FieldAE.section_memLp_iff haarAddCircle (G i) (hG i) p).mp (hGp i hi))
  have hAB:A=∑i∈s,B i:=by
    apply Lp.ext
    filter_upwards [ha,(Filter.eventually_all_finset s).mpr hb,Lp.coeFn_fun_finsetSum s B,he] with x ha hb hs he
    rw [ha,hs,he]
    exact Finset.sum_congr rfl (fun i hi=>(hb i hi).symm)
  change OneInputOperator.besselHalf Λ ρ hΛ hρ A=∑i∈s,OneInputOperator.besselHalf Λ ρ hΛ hρ (B i)
  rw [hAB,map_sum]
end SHE.NativeBesselFiniteIdentity
