module

public import SHE.NativeCurrentSourceEnergy
public import SHE.JointWordObserve
public import SHE.PairedAssignedTelescope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.JointCurrentDifference
open Set MeasureTheory Real StoppedFourier WordRecursion NativeHeatObservation DyadicApproximation
  PhysicalProfile GaussianAssignmentBlocks GaussianCoordinates
local instance jointCurrentDifference_period : Fact (0<2*π):=⟨by positivity⟩
open scoped NNReal
variable {Ω:Type*} {n:ℕ}

/-- The exact native joint current vector, without imposing a Gaussian
law on the actual state. -/
def state (Λ:ℝ) (U V:ℝ≥0×Ω→RealL2) (Z:Fin n→Observation) (q:ℝ) (ω:Ω):State n:=
  JointWordObserve.evaluate Λ (fun t=>embed (U (t.toNNReal,ω)))
    (fun t=>embed (V (t.toNNReal,ω)))
    (PredictableScalarField.wordField U ω) (PredictableScalarField.wordField V ω) Z q

/-- Original stops control damping and original targets control heat
age. At the newest target=q the exact scalar point is retained. -/
theorem coordinate (Λ:ℝ) (U V:ℝ≥0×Ω→RealL2) (Z:Fin n→Observation) (q:ℝ) (ω:Ω) (i:Fin n):
    state Λ U V Z q ω i-state Λ U U Z q ω i=
      exp (-Λ*((Z i).stop-q))*NativeCurrentSourceEnergy.value
        (fun ω=>U (q.toNNReal,ω)) (fun ω=>V (q.toNNReal,ω)) ((Z i).target-q) (ω,(Z i).center):=by
  unfold state JointWordObserve.evaluate WordRecursion.observe
  simp only [WithLp.ofLp_toLp]
  by_cases ht:q<(Z i).target
  · simp only [if_pos ht,sub_self,mul_zero,add_zero,NativeCurrentSourceEnergy.value,
      if_pos (sub_pos.mpr ht),map_sub]
    rw [←PhysicalProfile.physicalHeatMean_difference (sub_pos.mpr ht)
      (embed (V (q.toNNReal,ω))) (embed (U (q.toNNReal,ω))) (Z i).center]
    ring
  · have hτ:¬0<(Z i).target-q:=by linarith
    simp only [if_neg ht,NativeCurrentSourceEnergy.value,if_neg hτ,PredictableScalarField.wordField,
      PredictableScalarField.nativeField,PredictableScalarField.unitField]
    ring

theorem abs_coordinate_le (Λ:ℝ) (hΛ:0≤Λ) (U V:ℝ≥0×Ω→RealL2)
    (Z:Fin n→Observation) (q:ℝ) (ω:Ω) (i:Fin n) (hstop:q≤(Z i).stop):
    |state Λ U V Z q ω i-state Λ U U Z q ω i|≤
      |NativeCurrentSourceEnergy.value (fun ω=>U (q.toNNReal,ω)) (fun ω=>V (q.toNNReal,ω))
        ((Z i).target-q) (ω,(Z i).center)|:=by
  rw [coordinate,abs_mul,abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))

theorem root_source_le (Λ:ℝ) (hΛ:0≤Λ) (U V:ℝ≥0×Ω→RealL2)
    (Z:Fin n→Observation) (q:ℝ) (ω:Ω) (g:Fin 1→Fin n)
    {ν χ:ℝ} (hν:0≤ν) (hχ:0≤χ) (hstop:q≤(Z (g 0)).stop):
    (min 1 (ν*‖projection g (state Λ U V Z q ω-state Λ U U Z q ω)‖))^χ≤
      ν^χ*|NativeCurrentSourceEnergy.value (fun ω=>U (q.toNNReal,ω))
        (fun ω=>V (q.toNNReal,ω)) ((Z (g 0)).target-q) (ω,(Z (g 0)).center)|^χ:=by
  have hs:=ScalarNormalizedRootPair.source_bound hν hχ g (state Λ U V Z q ω) (state Λ U U Z q ω)
  exact hs.trans (mul_le_mul_of_nonneg_left (rpow_le_rpow (abs_nonneg _)
    (abs_coordinate_le Λ hΛ U V Z q ω (g 0) hstop) hχ) (rpow_nonneg hν _))

theorem rough_source_le (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (hΛ:0≤Λ)
    (U V:ℝ≥0×Ω→RealL2) (Z:Fin n→Observation) (q:ℝ) (ω:Ω)
    {r m:ℕ} (choices:List (Fin r×Fin m)) (factor:Fin m) (i:Fin n)
    {χ:ℝ} (hχ:0≤χ) (hstop:q≤(Z i).stop) (newBaseline oldBaseline:ℝ):
    PairedRoughWordMoments.source P choices factor χ (state Λ U V Z q ω) (state Λ U U Z q ω)
      i newBaseline oldBaseline≤
      max 1 (P.holder^(χ/P.exponent))*|NativeCurrentSourceEnergy.value
        (fun ω=>U (q.toNNReal,ω)) (fun ω=>V (q.toNNReal,ω)) ((Z i).target-q) (ω,(Z i).center)|^χ+
        |newBaseline-oldBaseline|^(χ/P.exponent):=by
  have hc:=rpow_le_rpow (abs_nonneg _) (abs_coordinate_le Λ hΛ U V Z q ω i hstop) hχ
  unfold PairedRoughWordMoments.source
  split_ifs with hb
  · unfold NormalizedPairedLeaf.source
    exact add_le_add (mul_le_mul
      (le_max_right _ _) hc (rpow_nonneg (abs_nonneg _) _) (le_max_left _ _ |>.trans' zero_le_one)) le_rfl
  · exact (hc.trans (le_mul_of_one_le_left (rpow_nonneg (abs_nonneg _) _) (le_max_left _ _))).trans
      (le_add_of_nonneg_right (rpow_nonneg (abs_nonneg _) _))

end SHE.JointCurrentDifference
