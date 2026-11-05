module

public import SHE.FiniteReferenceSplice
public import SHE.FirstGammaAffine
public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FiniteSpliceInitial
open Set MeasureTheory PredictableL2 StoppedItoInputs PastItoInputs GaussianIncrement
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H v : ℝ≥0)

theorem stop_post_self (u : Process (E:=C) 𝓕 μ H) : stop 𝓕 μ H (v:ℝ) (post 𝓕 μ H v u)=0 := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [stop_ae 𝓕 μ H (v:ℝ) (post 𝓕 μ H v u),post_ae 𝓕 μ H v u,
    ae_eq_of_ae_eq_trim (Lp.coeFn_zero C 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hs hp hz
  rw [hz,hs]
  by_cases hlt : p.1<v
  · rw [indicator_of_mem (show p∈before (Ω:=Ω) (v:ℝ) by exact_mod_cast hlt),hp,
      ite_eq_right (not_lt.mpr hlt.le)]
    rfl
  · rw [indicator_of_notMem (show p∉before (Ω:=Ω) (v:ℝ) by exact_mod_cast hlt)]
    rfl

variable {n : ℕ} (R S : Fin n→Process (E:=C) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H) (z : State n)

/-- The frozen reference and original martingale have the SAME actual
F_v value; no independent restarted initial variable is supplied. -/
theorem joint_at_past : ∀ᵐ ω∂μ,
    FiniteComparisonTest.left n
      (StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z)
        (FiniteReferenceSplice.jointRows 𝓕 μ H v R S) v ω)=
    FiniteComparisonTest.right n
      (StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z)
        (FiniteReferenceSplice.jointRows 𝓕 μ H v R S) v ω) := by
  filter_upwards with ω
  apply PiLp.ext
  intro i
  simp only [FiniteComparisonTest.left_apply,FiniteComparisonTest.right_apply,
    StandardFiniteIto.vectorIntegral,FiniteReferenceSplice.jointInitial,
    FiniteReferenceSplice.jointRows,WithLp.ofLp_toLp,Fin.append_left,Fin.append_right]
  rw [FiniteReferenceSplice.stopped_rows,map_add,min_self,stop_post_self,map_zero]
  -- Point evaluation of the sum is removed at the Lp level.
  simp only [add_zero]

/-- At a common initial pair, the time-dependent current affine map
and constant reference map agree, including the frozen D coordinate. -/
theorem affine_equal {m : ℕ} (Λ θ t : ℝ) (target : Fin m→ℝ) (w : FirstGammaAffine.Space m)
    (h : FiniteComparisonTest.left (m+m) w=FiniteComparisonTest.right (m+m) w) :
    FirstGammaAffine.current m Λ θ target t w=FirstGammaAffine.reference m Λ θ target w := by
  have hU : FirstGammaAffine.currentU m w=FirstGammaAffine.frozenU m w := congrArg (ObservationBlockMaps.first m) h
  have hD : FirstGammaAffine.currentD m w=FirstGammaAffine.pastD m w := congrArg (ObservationBlockMaps.second m) h
  ext i
  simp only [FirstGammaAffine.current,DampedAffineGaussian.linear,FirstGammaAffine.baseCurrent,
    FirstGammaAffine.dynamic,FirstGammaAffine.reference,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    sub_apply,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,PiLp.zero_apply,smul_eq_mul,hU,hD,sub_self,mul_zero,add_zero]

end SHE.FiniteSpliceInitial
