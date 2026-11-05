module
public import SHE.NativeBesselSectionEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselFiniteSumEnergy
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {P I:Type*}[MeasurableSpace P]
variable (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)

/-- The actual native sections commute with a finite scalar sum after
all original spatial sections have their L2 applicability established. -/
theorem value (s:Finset I)(G:I→P×HeatCircle→ℂ)(hG:∀i,Measurable (G i))
    (p:P)(hp:∀i∈s,MemLp (fun x=>G i (p,x)) 2 haarAddCircle):
    NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z=>∑i∈s,G i z) p=
      ∑i∈s,NativeBesselFieldAE.value Λ ρ hΛ hρ (G i) p:=by
  have hs:MemLp (fun x=>∑i∈s,G i (p,x)) 2 haarAddCircle:=by
    classical
    induction s using Finset.induction_on with
    | empty=>simpa using (MemLp.zero (μ:=haarAddCircle) (p:=2) (E:=ℂ))
    | @insert i s hi ih=>
      simp only [Finset.mem_insert] at hp
      convert! (hp i (Or.inl rfl)).add (ih (fun j hj=>hp j (Or.inr hj))) using 1
      funext x
      simp only [Finset.sum_insert hi,Pi.add_apply]
  exact NativeBesselFiniteIdentity.finite_sum Λ ρ hΛ hρ s _
    (Finset.measurable_sum _ (fun i _=>hG i)) G hG p hs hp (ae_of_all _ (fun _=>rfl))

/-- Scalar product energy controls the exact finite sum of actual native
sections with the true massive Bessel gain. -/
theorem energy (η:Measure P)[SFinite η](s:Finset I)(G:I→P×HeatCircle→ℂ)
    (hG:∀i,Measurable (G i))
    (hp:∀p i,i∈s→MemLp (fun x=>G i (p,x)) 2 haarAddCircle)
    (hi:Integrable (fun z=>‖∑i∈s,G i z‖^2) (η.prod haarAddCircle))
    (R:ℝ)(hR:(∫z,‖∑i∈s,G i z‖^2 ∂η.prod haarAddCircle)≤R):
    Integrable (fun p=>‖∑i∈s,NativeBesselFieldAE.value Λ ρ hΛ hρ (G i) p‖^2) η ∧
      (∫p,‖∑i∈s,NativeBesselFieldAE.value Λ ρ hΛ hρ (G i) p‖^2 ∂η)≤Λ^(-ρ)*R:=by
  have he(p:P):NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z=>∑i∈s,G i z) p=
      ∑i∈s,NativeBesselFieldAE.value Λ ρ hΛ hρ (G i) p:=
    value Λ ρ hΛ hρ s G hG p (hp p)
  simpa only [he] using NativeBesselSectionEnergy.energy_of_integral_bound Λ ρ hΛ hρ η
    (fun z=>∑i∈s,G i z) (Finset.measurable_sum _ (fun i _=>hG i)) hi R hR
end SHE.NativeBesselFiniteSumEnergy
