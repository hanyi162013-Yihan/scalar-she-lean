module

public import SHEStochastic.VectorHeat
public import SHE.HilbertColumns
public import SHE.HilbertColumnMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.VectorHilbertColumns
open SHE SHE.DyadicApproximation
open scoped ENNReal

variable {d ι : Type*} [Fintype d] [DecidableEq d]

def lift (i : d) (u : RealL2) : VectorHeat.Physical (d := d) :=
  VectorHeat.coordinates.symm (PiLp.single 2 i u)

theorem norm_lift (i : d) (u : RealL2) : ‖lift i u‖=‖u‖ := by
  rw [lift, LinearIsometryEquiv.norm_map, PiLp.norm_single]

theorem summable (K : HilbertColumns.Space ι RealL2) :
    Summable (fun p : d × ι => ‖lift p.1 (K p.2)‖^2) := by
  simp_rw [norm_lift]
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun _ => ?_, ⟨_, hasSum_fintype _⟩⟩
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp K).summable (by norm_num : 0 < (2 : ENNReal).toReal)

/-- Finite state components reuse any existing scalar Hilbert-column
kernel, with the exact dimension factor in its squared norm. -/
def columns (K : HilbertColumns.Space ι RealL2) :
    HilbertColumns.Space (d × ι) (VectorHeat.Physical (d := d)) :=
  HilbertColumns.ofSummable (fun p => lift p.1 (K p.2)) (summable K)

theorem norm_sq (K : HilbertColumns.Space ι RealL2) :
    ‖columns (d := d) K‖^2=(Fintype.card d : ℝ)*‖K‖^2 := by
  rw [HilbertColumns.norm_sq, HilbertColumns.norm_sq]
  change (∑' p : d × ι, ‖lift p.1 (K p.2)‖^2)=_
  rw [(summable K).tsum_prod' (fun _ => by
    simpa only [norm_lift, ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp K).summable (by norm_num : 0 < (2 : ENNReal).toReal)), tsum_fintype]
  simp only [norm_lift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem heat_lift (t : ℝ) (i : d) (u : RealL2) :
    VectorHeat.heat t (lift i u)=lift i (RealHeat.realHeat t u) := by
  apply VectorHeat.coordinates.injective
  apply PiLp.ext
  intro j
  rw [VectorHeat.coordinate_heat]
  change RealHeat.realHeat t (VectorHeat.coordinates (VectorHeat.coordinates.symm (PiLp.single 2 i u)) j)=
    VectorHeat.coordinates (VectorHeat.coordinates.symm (PiLp.single 2 i (RealHeat.realHeat t u))) j
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  by_cases h : j=i <;> simp [PiLp.single_apply, h]


theorem heat_columns (t : ℝ) (K : HilbertColumns.Space ι RealL2) :
    HilbertColumns.mapCLM (VectorHeat.heat (d := d) t) (columns K)=
      columns (HilbertColumns.mapCLM (RealHeat.realHeat t) K) := by
  apply lp.ext
  funext p
  exact heat_lift t p.1 (K p.2)

end SHEStochastic.VectorHilbertColumns
