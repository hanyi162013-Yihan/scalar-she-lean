module
public import SHE.NativeContinuousPath
public import SHE.RawCylindricalCoordinates
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.CanonicalContinuousStateDriver
open MeasureTheory PredictableL2 Set
open scoped NNReal ENNReal
variable{Ω E ι:Type*}[MeasurableSpace Ω][Countable ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(H:ℝ≥0)

/-- Canonical continuous state paths and countably many continuous scalar
driver paths form a standard Borel space, even when the original sample
space carries no topology or regular conditional probabilities. -/
abbrev Space:=C(Icc (0:ℝ) (H:ℝ),E) × (ι→C(Icc (0:ℝ) (H:ℝ),ℝ))

instance space_standardBorel:StandardBorelSpace (Space (E:=E) (ι:=ι) H):=inferInstance
instance space_nonempty:Nonempty (Space (E:=E) (ι:=ι) H):=inferInstance

variable(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω))
variable(W:ι→ℝ≥0→Ω→ℝ)(hd:∀i ω,Continuous (fun t=>W i t ω))

def bundle(ω:Ω):Space (E:=E) (ι:=ι) H:=
  (NativeContinuousPath.path H U hc ω,fun i=>NativeContinuousPath.path H (W i) (hd i) ω)

theorem measurable_bundle(hU:Measurable (Function.uncurry U))
    (hW:∀i,Measurable (Function.uncurry (W i))):
    Measurable (bundle H U hc W hd):=
  (NativeContinuousPath.measurable_path H U hc hU).prodMk
    (measurable_pi_iff.mpr (fun i=>NativeContinuousPath.measurable_path H (W i) (hd i) (hW i)))

@[simp] theorem state_eval(ω:Ω)(t:Icc (0:ℝ) (H:ℝ)):
    (bundle H U hc W hd ω).1 t=U t.val.toNNReal ω:=rfl

@[simp] theorem driver_eval(ω:Ω)(i:ι)(t:Icc (0:ℝ) (H:ℝ)):
    (bundle H U hc W hd ω).2 i t=W i t.val.toNNReal ω:=rfl

/-- The actual canonical joint law, obtained by an ordinary measurable
pushforward. Future conditional laws may be disintegrated on this space. -/
def law(μ:Measure Ω):Measure (Space (E:=E) (ι:=ι) H):=
  μ.map (bundle H U hc W hd)

instance law_probability(μ:Measure Ω)[IsProbabilityMeasure μ]:
    IsProbabilityMeasure (law H U hc W hd μ):=by
  unfold law
  infer_instance

section Actual
variable{C:Type*}[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(e:ι→C)(he:Orthonormal ℝ e)
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable(hpos:0<H)

def actual:Ω→Space (E:=E) (ι:=ι) H:=
  bundle H U hc (RawCylindricalCoordinates.continuous 𝓕 μ H e J)
    (fun i=>BoundedStoppedVersion.continuous_version 𝓕 μ H J
      (RawCylindricalCoordinates.row 𝓕 μ H e i) hpos)

include he in
/-- On real horizons at most one, ordinary BDG constructs the continuous
coordinate versions of the SAME original integral internally. For a
larger horizon, `bundle` accepts given ordinary continuous versions. -/
theorem actual_measurable(hU:Measurable (Function.uncurry U))
    (hH:(H:ℝ)≤1)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B):
    Measurable (actual H U hc 𝓕 μ e J hpos):=by
  apply measurable_bundle H U hc _ _ hU
  intro i
  exact ((BoundedStoppedVersion.predictable_version 𝓕 μ H J
    (RawCylindricalCoordinates.row 𝓕 μ H e i) hH hpos hnull B hBDG
    (by norm_num:0≤(1:ℝ)) (RawCylindricalCoordinates.row_norm 𝓕 μ H e he i)).mono
      (predictable_le_product 𝓕)).measurable

include he in
theorem actual_driver_ae(hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
    (i:ι)(t:Icc (0:ℝ) (H:ℝ)):
    (fun ω=>(actual H U hc 𝓕 μ e J hpos ω).2 i t)=ᵐ[μ]
      RawCylindricalCoordinates.value 𝓕 μ H e J i t.val.toNNReal:=
  RawCylindricalCoordinates.continuous_ae 𝓕 μ H e he J B hBDG hH hpos i t.val.toNNReal

@[simp] theorem actual_state_eval(ω:Ω)(t:Icc (0:ℝ) (H:ℝ)):
    (actual H U hc 𝓕 μ e J hpos ω).1 t=U t.val.toNNReal ω:=rfl
end Actual
end SHE.CanonicalContinuousStateDriver
