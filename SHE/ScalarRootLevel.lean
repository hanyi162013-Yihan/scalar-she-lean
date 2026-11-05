module

public import SHE.ScalarRootUncutExpansion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ScalarRootLevel
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel
open SmoothCylinders UniformSmooth
local instance scalarRootLevel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (R : ReferenceData) (T : ℝ) (hbase : R.base≤T) (hhorizon : T≤R.horizon)
variable (g : ℝ→ℝ) (hg : BoundedSmooth g) (ψ : HeatCircle→ℝ) (hψ : Measurable ψ)
variable {W : ℝ} (hW : 0≤W) (hbψ : ∀ x,|ψ x|≤W)

/-- The literal scalar terminal observation: stop=target=T and the
spatial root parameter is its actual native-circle center. -/
def level : Level R HeatCircle 1 where
  observations := {
    observations := fun x _ => ⟨T,T,x⟩
    stop_measurable := fun _ => measurable_const
    target_measurable := fun _ => measurable_const
    center_measurable := fun _ => measurable_id }
  terminal := fun _ => T
  terminal_measurable := measurable_const
  terminal_base := fun _ => hbase
  terminal_horizon := fun _ => hhorizon
  targets_after := fun _ _ => le_rfl
  stops_after := fun _ _ => le_rfl
  test := fun x z => ψ x*g (z 0)
  test_uniform := by
    have hp : UniformBoundedSmooth (fun x (_ : WordRecursion.State 1) => ψ x) :=
      UniformBoundedSmooth.parameter_const ψ hW (fun x => by simpa only [Real.norm_eq_abs] using hbψ x)
    have hg' : UniformBoundedSmooth (fun _ : HeatCircle => g) := UniformBoundedSmooth.fixed hg
    exact hp.mul (hg'.comp_right (EuclideanSpace.proj (0:Fin 1)))
  test_measurable := (hψ.comp measurable_fst).mul
    (hg.smooth.continuous.measurable.comp ((EuclideanSpace.proj (0:Fin 1)).continuous.measurable.comp measurable_snd))

theorem terminal (x : HeatCircle) : (level R T hbase hhorizon g hg ψ hψ hW hbψ).terminal x=T := rfl
theorem stop (x : HeatCircle) : ((level R T hbase hhorizon g hg ψ hψ hW hbψ).observations.observations x 0).stop=T := rfl
theorem target (x : HeatCircle) : ((level R T hbase hhorizon g hg ψ hψ hW hbψ).observations.observations x 0).target=T := rfl
theorem center (x : HeatCircle) : ((level R T hbase hhorizon g hg ψ hψ hW hbψ).observations.observations x 0).center=x := rfl

theorem test_eq (x : HeatCircle) (r : ℝ) :
    (level R T hbase hhorizon g hg ψ hψ hW hbψ).test x (ScalarRootHeatLeaf.scalarState r)=ψ x*g r := rfl

end SHE.ScalarRootLevel
