module

public import SHE.ControlledJointMeanIdentity
public import SHE.NativePairHybridMoments
public import SHE.MixedNativePairFuture

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.JointInterpolationAlgebra
open Set MeasureTheory Real StoppedFourier NativeHeatObservation DyadicApproximation
  StoppedGaussianScore ControlledJointWeightedWord
open scoped NNReal
local instance jointInterpolationAlgebra_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

def current (Λ q θ : ℝ) (U V : RealL2) (Z : Fin n→WordRecursion.Observation) : WordRecursion.State n :=
  WithLp.toLp 2 (fun i=>functional ((Z i).target-q) (Z i).center U+
    θ*exp (-Λ*((Z i).stop-q))*functional ((Z i).target-q) (Z i).center (V-U))

theorem current_one (Λ q : ℝ) (U V : RealL2) (Z : Fin n→WordRecursion.Observation) (i : Fin n) :
    current Λ q 1 U V Z i=functional ((Z i).target-q) (Z i).center U+
      exp (-Λ*((Z i).stop-q))*functional ((Z i).target-q) (Z i).center (V-U) := by
  simp only [current,WithLp.ofLp_toLp,one_mul]

theorem current_eq_jointMeanVector (Λ q θ : ℝ) (U V : RealL2)
    (Z : Fin n→WordRecursion.Observation) (a : Fin n→UnitAddCircle)
    (hcenter : ∀ i,nativeCenter a i=(Z i).center) (hgap : ∀ i,q<(Z i).target) :
    current Λ q θ U V Z=jointMeanVector (fun i=>(Z i).stop) (fun i=>(Z i).target) a q Λ
      (embed U) (embed (V-U)) θ := by
  apply PiLp.ext
  intro i
  rw [jointMeanVector_apply,hcenter i,←functional_physical (sub_pos.mpr (hgap i)),
    ←functional_physical (sub_pos.mpr (hgap i))]
  rfl

theorem damped_parameter_bound {Λ q σ θ : ℝ} (hΛ : 0≤Λ) (hσ : q≤σ) (hθ : |θ|≤1) :
    |θ*exp (-Λ*(σ-q))|≤1 := by
  rw [abs_mul,abs_of_pos (exp_pos _)]
  have he : exp (-Λ*(σ-q))≤1 := exp_le_one_iff.mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_right hθ (exp_pos _).le).trans (by simpa only [one_mul] using he)

/-- The native target-stop identity is indispensable here. It makes the
full controlled profile mean equal to the exact deterministic hybrid
center; current-time and target-time damping are not conflated. -/
theorem centered_native_eq_hybrid (Λ θ : ℝ) (q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T)
    (x : HeatCircle) (U V u v : RealL2) :
    functional (T-(q:ℝ)) x U+θ*exp (-Λ*(T-(q:ℝ)))*functional (T-(q:ℝ)) x (V-U)-
        ControlledProfile.mean Λ (embed u) (embed (v-u)) (θ,(T,x))=
      functional (T-(q:ℝ)) x (U+(θ*exp (-Λ*(T-(q:ℝ)))) • (V-U))-
        (functional T x u+(θ*exp (-Λ*(T-(q:ℝ))))*exp (-Λ*(q:ℝ))*functional T x (v-u)) := by
  have ht : 0<T := q.2.trans_lt hT
  have he : exp (-Λ*(T-(q:ℝ)))*exp (-Λ*(q:ℝ))=exp (-Λ*T) := by
    rw [←exp_add]
    congr 1
    ring
  simp only [ControlledProfile.mean,map_add,map_smul,smul_eq_mul]
  rw [←functional_physical ht,←functional_physical ht]
  rw [←he]
  ring

end SHE.JointInterpolationAlgebra
