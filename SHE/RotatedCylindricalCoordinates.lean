module
public import SHE.RotatedItoAlgebra
public import SHE.BoundedStoppedVersion
public import SHE.BoundedVectorIntegral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.RotatedCylindricalCoordinates
open MeasureTheory PredictableL2 StoppedItoInputs PredictableItoRotation
open scoped NNReal ENNReal
variable{Ω A C ι:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup A][InnerProductSpace ℝ A][MeasurableSpace A][BorelSpace A]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C]
variable[SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(Φ:(ℝ≥0×Ω)→A→ₗᵢ[ℝ]C)
variable(hΦ:@Measurable ((ℝ≥0×Ω)×A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p=>Φ p.1 p.2))

theorem constant_memLp(e:A):@MemLp _ _ 𝓕.predictable _ _ (fun _:ℝ≥0×Ω=>e) 2
    ((energyMeasure μ H).trim (predictable_le_product 𝓕)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only[energyMeasure];infer_instance
  exact memLp_const e

def constant(e:A):Process (E:=A) 𝓕 μ H:=
  (constant_memLp 𝓕 μ H e).toLp (fun _=>e)

theorem constant_ae(e:A):constant 𝓕 μ H e=ᵐ[energyMeasure μ H] (fun _=>e):=
  ae_eq_of_ae_eq_trim (constant_memLp 𝓕 μ H e).coeFn_toLp

/-- Actual predictable orthogonally rotated deterministic test input. -/
def row(e:A):Process (E:=C) 𝓕 μ H:=
  processIsometry 𝓕 μ H Φ hΦ (constant 𝓕 μ H e)

theorem row_ae(e:A):row 𝓕 μ H Φ hΦ e=ᵐ[energyMeasure μ H] (fun p=>Φ p e):=by
  filter_upwards [processIsometry_ae 𝓕 μ H Φ hΦ (constant 𝓕 μ H e),constant_ae 𝓕 μ H e] with p hp he
  exact hp.trans (congrArg (Φ p) he)

theorem row_norm(e:A):∀ᵐp∂energyMeasure μ H,‖row 𝓕 μ H Φ hΦ e p‖^2=‖e‖^2:=by
  filter_upwards [row_ae 𝓕 μ H Φ hΦ e] with p hp
  rw [hp,(Φ p).norm_map]

variable[Countable ι][DecidableEq ι](e:ι→A)(he:Orthonormal ℝ e)

include he in
/-- One ORIGINAL energy event identifies every pair of countably many
rotated rows with the original orthonormal Gram matrix. -/
theorem all_gram:∀ᵐp∂energyMeasure μ H,∀i j:ι,
    inner ℝ (row 𝓕 μ H Φ hΦ (e i) p) (row 𝓕 μ H Φ hΦ (e j) p)=if i=j then 1 else 0:=by
  classical
  filter_upwards [ae_all_iff.mpr (fun i:ι=>row_ae 𝓕 μ H Φ hΦ (e i))] with p hp i j
  rw [hp i,hp j,(Φ p).inner_map_map]
  exact orthonormal_iff_ite.mp he i j

variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

/-- Countably many actual coordinate processes, each a continuous version
of a stopped integral on the SAME original J. -/
def coordinate(i:ι)(t:ℝ≥0)(ω:Ω):ℝ:=
  BoundedStoppedVersion.version 𝓕 μ H J (row 𝓕 μ H Φ hΦ (e i)) t ω

include he in
theorem continuous_coordinate(hH0:0<H)(i:ι)(ω:Ω):
    Continuous (fun t=>coordinate 𝓕 μ H Φ hΦ e J i t ω):=
  BoundedStoppedVersion.continuous_version 𝓕 μ H J (row 𝓕 μ H Φ hΦ (e i)) hH0 ω

include he in
theorem coordinate_ae(hH:(H:ℝ)≤1)(hH0:0<H)(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
    (t:ℝ≥0):
    ∀ᵐω∂μ,∀i:ι,coordinate 𝓕 μ H Φ hΦ e J i t ω=
      J.integral (stop 𝓕 μ H (min t H) (row 𝓕 μ H Φ hΦ (e i))) ω:=by
  apply ae_all_iff.mpr
  intro i
  exact BoundedStoppedVersion.version_ae 𝓕 μ H J (row 𝓕 μ H Φ hΦ (e i)) hH hH0 B hBDG
    (by norm_num:0≤(1:ℝ)) ((row_norm 𝓕 μ H Φ hΦ (e i)).mono (fun p hp=>by
      rw [hp,he.norm_eq_one i];norm_num)) t

include he in
theorem predictable_coordinate(hH:(H:ℝ)≤1)(hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)(i:ι):
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (coordinate 𝓕 μ H Φ hΦ e J i)):=
  BoundedStoppedVersion.predictable_version 𝓕 μ H J (row 𝓕 μ H Φ hΦ (e i)) hH hH0 hnull B hBDG
    (by norm_num:0≤(1:ℝ)) ((row_norm 𝓕 μ H Φ hΦ (e i)).mono (fun p hp=>by
      rw [hp,he.norm_eq_one i];norm_num))

/-- All finite projections use these SAME coordinate paths, so their
restriction consistency is pointwise, not a fresh version choice. -/
def projection{n:ℕ}(a:Fin n→ι)(t:ℝ≥0)(ω:Ω):WordRecursion.State n:=
  WithLp.toLp 2 (fun i=>coordinate 𝓕 μ H Φ hΦ e J (a i) t ω)

theorem projection_consistent{m n:ℕ}(a:Fin n→ι)(b:Fin m→ι)(f:Fin m→Fin n)
    (hf:∀i,b i=a (f i))(t:ℝ≥0)(ω:Ω):
    projection 𝓕 μ H Φ hΦ e J b t ω=
      WithLp.toLp 2 (fun i=>projection 𝓕 μ H Φ hΦ e J a t ω (f i)):=by
  apply PiLp.ext
  intro i
  simp only[projection,WithLp.ofLp_toLp,hf]

end SHE.RotatedCylindricalCoordinates
